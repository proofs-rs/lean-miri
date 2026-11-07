import Miri.Input.CallResolution

open Lean Miri Miri.Input

private def must (value : Except ε α) [ToString ε] : IO α :=
  match value with
  | .ok value => pure value
  | .error error => throw (IO.userError (toString error))

private def replace (table : MIR.SharedTable α) (id : Nat) (value : α) : IO (MIR.SharedTable α) := do
  if bound : id < table.size then return table.set id (some value) bound
  throw (IO.userError "test table entry missing")

private def reject (runtime : RuntimeMetadata) (id : Nat) (label : String) : IO Unit := do
  let cache := CallResolution.prepareFunctionAbiCache runtime
  match CallResolution.functionAbiId runtime id (some cache) with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"invalid ABI accepted: {label}")

private def withFunction (runtime : RuntimeMetadata) (id : Nat) (abi : FunctionAbiData) : IO RuntimeMetadata := do
  let functions ← replace runtime.source.abiTables.functions id (.ok abi)
  return {runtime with source := {runtime.source with abiTables := {runtime.source.abiTables with functions}}}

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "usage: AbiTableFailures <export.json>")
  let decoded ← must (decodeRuntimeJson (← IO.FS.readFile path))
  let runtime ← must (RuntimeMetadata.ofDocument decoded.document)
  let some (id, abi) := runtime.source.abiTables.functions.toList.zipIdx.findSome? (fun (entry,id) =>
      match entry with | some (.ok abi) => some (id,abi) | _ => none)
    | throw (IO.userError "fixture has no function ABI")
  let _ ← must (CallResolution.functionAbiById runtime id)
  let arguments ← must (runtime.source.abiTables.argumentLists.lookup abi.arguments)
  reject (← withFunction runtime id {abi with fixedCount := arguments.size + 1}) id "arity"
  reject (← withFunction runtime id {abi with fixedCount := 2^32}) id "u32 argument count overflow"
  reject (← withFunction runtime id {abi with arguments := runtime.source.abiTables.argumentLists.size}) id "argument list ID"
  reject (← withFunction runtime id {abi with returnValue := runtime.source.abiTables.arguments.size}) id "return argument ID"
  reject runtime runtime.source.abiTables.functions.size "function ID"
  let argument ← must (runtime.source.abiTables.arguments.lookup abi.returnValue)
  let invalidType ← replace runtime.source.abiTables.arguments abi.returnValue {argument with typeId := runtime.source.types.size}
  reject {runtime with source := {runtime.source with abiTables := {runtime.source.abiTables with arguments := invalidType}}} id "type ID"
  let invalidLayout ← replace runtime.source.abiTables.arguments abi.returnValue {argument with layoutId := some runtime.layouts.size}
  reject {runtime with source := {runtime.source with abiTables := {runtime.source.abiTables with arguments := invalidLayout}}} id "layout ID"
  let missingLayout ← replace runtime.source.abiTables.arguments abi.returnValue {argument with layoutId := none}
  reject {runtime with source := {runtime.source with abiTables := {runtime.source.abiTables with arguments := missingLayout}}} id "missing physical layout"
  let some layoutId := argument.layoutId | throw (IO.userError "fixture lacks physical layout")
  let layout ← must (runtime.source.layoutTable.lookup layoutId)
  let layoutTable ← replace runtime.source.layoutTable layoutId {layout with sizeBytes := some (2^64)}
  let oversized ← must (RuntimeMetadata.ofDocument {runtime.source with layoutTable})
  reject oversized id "physical layout size overflow"
  IO.println "ABI table failures: PASS (arity, overflow, missing data and invalid IDs)"
