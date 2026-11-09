import Miri.Input.CallResolution

open Lean Miri.Input

private def must (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def rejects (value : Except String α) (message : String) : IO Unit :=
  match value with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

private def set (value : Json) (key : String) (child : Json) : Except String Json := do
  let fields ← value.getObj?
  pure (Json.mkObj ((key, child) :: fields.toList.filter (fun item => item.1 != key)))

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected exporter MIR input")
  let decoded ← must (decodeJson (← IO.FS.readFile path))
  let runtime ← must ((RuntimeMetadata.ofDocument decoded.document).mapError toString)
  check (!runtime.source.functionAbis.isEmpty) "fixture contains no function ABI definitions"
  for (abi, id) in runtime.source.functionAbis.toList.zipIdx do
    let parsed ← must (DecoderValues.decodeCompilerFunctionAbi abi.payload)
    check (parsed.arguments.map (·.payload) == abi.arguments.map (·.payload) &&
      parsed.returnValue.payload == abi.returnValue.payload &&
      parsed.callingConvention.payload == abi.callingConvention.payload &&
      parsed.fixedCount == abi.fixedCount && parsed.canUnwind == abi.canUnwind &&
      parsed.cVariadic == abi.cVariadic) "typed ABI table differs from its definition"
    check (CallResolution.functionAbiJson runtime (toJson id) ==
      CallResolution.functionAbi runtime abi) "numeric ABI lookup differs from typed conversion"
  rejects (CallResolution.functionAbiId runtime runtime.source.functionAbis.size)
    "out of bounds ABI accepted"
  rejects (CallResolution.functionAbiJson runtime (Json.mkObj [("fn_abi_id", toJson (0 : Nat))]))
    "object ABI reference accepted"
  let some sample := runtime.source.functionAbis[0]? | throw (IO.userError "missing first function ABI")
  let invalidArity := { sample with fixedCount := sample.arguments.size + 1 }
  let arityRuntime := { runtime with source := { runtime.source with functionAbis := #[invalidArity] } }
  match CallResolution.functionAbiId arityRuntime 0 with
  | .error message => check (message.contains "fixed_count exceeds actual arguments") "arity diagnostic changed"
  | .ok _ => throw (IO.userError "ABI arity check bypassed")
  let invalidConvention := { sample with callingConvention :=
    { sample.callingConvention with kind := .arm, armCall := none } }
  let conventionRuntime := { runtime with source := { runtime.source with functionAbis := #[invalidConvention] } }
  rejects (CallResolution.functionAbiId conventionRuntime 0) "missing calling convention evidence accepted"
  let layoutId := sample.returnValue.layoutId
  let some layout := runtime.source.layouts[layoutId]? | throw (IO.userError "fixture return layout missing")
  let oversized := { layout with sizeBytes := some (2^64) }
  let sizeRuntime := { runtime with source := { runtime.source with
    functionAbis := #[sample], layouts := runtime.source.layouts.set! layoutId oversized } }
  match CallResolution.functionAbiId sizeRuntime 0 with
  | .error message => check (message.contains "u64 overflow") "physical size overflow diagnostic changed"
  | .ok _ => throw (IO.userError "ABI layout-size check bypassed")
  let invalidLayout := { sample.returnValue with layoutId := runtime.source.layouts.size }
  let layoutRuntime := { runtime with source := { runtime.source with
    functionAbis := #[{ sample with returnValue := invalidLayout }] } }
  rejects (CallResolution.functionAbiId layoutRuntime 0) "out of bounds physical layout accepted"
  let malformedLayout ← must (set layout.payload "field_offsets_bytes" (.str "not-an-array"))
  rejects (DecoderValues.decodeCompilerLayout malformedLayout) "malformed layout definition accepted"
  let returnJson ← must (sample.payload.getObjVal? "return")
  let inlineReturn ← must (set returnJson "layout" layout.payload)
  let inlineAbi ← must (set sample.payload "return" inlineReturn)
  rejects (DecoderValues.decodeCompilerFunctionAbi inlineAbi) "inline physical layout accepted at ID position"
  IO.println s!"typed ABI table: {runtime.source.functionAbis.size} definitions; bounds, arity, convention and physical layout checks passed"
