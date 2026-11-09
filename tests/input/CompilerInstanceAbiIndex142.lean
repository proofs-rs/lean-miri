import Miri.Input

open Lean Miri.Input Miri.ABI Miri.Interpreter

private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def linear (prepared : CompilerInstanceAbi.Prepared)
    (callee : CallInstance) (extra : Array Miri.MIR.TyId) : Except String (FnAbi Miri.MIR.TyId) := do
  let some entry := prepared.entries.find? (fun entry => entry.callee == callee && entry.extra == extra)
    | throw "missing exact full-instance/extra-argument FnAbi query"
  CallResolution.functionAbiId prepared.runtime (← entry.result)

private def set (value : Json) (key : String) (child : Json) : Except String Json := do
  let fields ← value.getObj?
  pure (Json.mkObj ((key, child) :: fields.toList.filter (fun item => item.1 != key)))

private def prepare (raw : Json) : Except String CompilerInstanceAbi.Prepared := do
  let decoded ← decodeJson raw.compress
  let runtime ← (RuntimeMetadata.ofDocument decoded.document).mapError toString
  let program ← lowerProgram decoded.document
  CompilerInstanceAbi.prepare runtime program

private def compare (prepared : CompilerInstanceAbi.Prepared) : IO Unit := do
  for entry in prepared.entries do
    check (CompilerInstanceAbi.abiOfInstance prepared entry.callee entry.extra ==
      linear prepared entry.callee entry.extra) "indexed ABI lookup differs from source-order lookup"
  check (CompilerInstanceAbi.abiOfInstance prepared prepared.program.input.instances.size #[] ==
    linear prepared prepared.program.input.instances.size #[]) "missing ABI query changed its error"

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected exporter MIR input")
  let raw ← must (Json.parse (← IO.FS.readFile path))
  let prepared ← must (prepare raw)
  check (!prepared.entries.isEmpty) "fixture contains no exact instance ABI queries"
  compare prepared
  let manual : CompilerInstanceAbi.Prepared := ⟨prepared.runtime, prepared.program, prepared.entries, none⟩
  compare manual
  let rows ← must ((raw.getObjVal? "compiler_instance_abis").bind Json.getArr?)
  let first := rows[0]!
  let duplicate ← must (set raw "compiler_instance_abis" (.arr (rows.push first)))
  let duplicated ← must (prepare duplicate)
  check (duplicated.entries.size == prepared.entries.size) "identical query evidence was duplicated"
  compare duplicated
  let some firstType := prepared.program.input.types[0]? | throw (IO.userError "missing first type")
  let typeId := firstType.id
  let extra ← must (set first "extra_argument_types" (.arr #[toJson typeId]))
  let extended ← must (set raw "compiler_instance_abis" (.arr (rows.push extra)))
  let extended ← must (prepare extended)
  compare extended
  let firstId ← must ((first.getObjVal? "instance_id").bind Json.getNat?)
  check (extended.entries.any fun entry => entry.callee == firstId && entry.extra == #[typeId])
    "ordered additional argument types were omitted from the exact query key"
  let abiId ← must ((first.getObjVal? "abi_query").bind Json.getNat?)
  if prepared.runtime.source.functionAbis.size > 1 then
    let otherId := if abiId == 0 then 1 else 0
    let conflicting ← must (set first "abi_query" (toJson otherId))
    let conflicting ← must (set raw "compiler_instance_abis" (.arr (rows.push conflicting)))
    match prepare conflicting with
    | .error message => check (message == "conflicting exact instance ABI evidence") "conflicting ABI query diagnostic changed"
    | .ok _ => throw (IO.userError "conflicting ABI IDs were accepted")
  IO.println s!"exact instance ABI IDs: {prepared.entries.size} queries; indexed/source-order parity, duplicates, conflicts and additional arguments checked"
