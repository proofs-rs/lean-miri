import Miri.Input.CompilerRuntimeQueries
import Miri.Input.Decoder

open Lean Miri.Input Miri.Interpreter

private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error e => throw (IO.userError e)
private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def set (j : Json) (key : String) (value : Json) : Json :=
  match j with
  | .obj fields => Json.mkObj ((key,value) :: fields.toList.filter (·.1 != key))
  | _ => Json.mkObj [(key,value)]

-- Mutations of genuine compiler input test the schema boundary, not guest safety.
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected genuine compiler export")
  let decoded ← must (decodeRuntimeJson (← IO.FS.readFile path))
  let program ← must (lowerCoreProgram decoded.document)
  let some ty := program.input.types[0]? | throw (IO.userError "missing fixture type")
  let row := Json.mkObj [("input_type_id", toJson ty.id),
    ("typing_env", .str "fully_monomorphized")]
  let fact := Json.mkObj [("status", .str "supported"),
    ("value", Json.mkObj [("type_id", toJson ty.id)])]
  let prepare := fun (rows : Array Json) (schema : Option Json) =>
    let raw := Json.mkObj ([("types", .arr rows), ("instances", .arr #[]),
      ("virtual", .arr #[])] ++ schema.toList.map ("type_query_schema", ·))
    let raw := set program.input.raw "compiler_runtime_queries" raw
    CompilerRuntimeQueries.prepare { program with
      input := { program.input with raw, allocationWorldValidation := none } }
  let marker := some (Json.str "source_operations_v1")
  let sparse ← must (prepare #[row] marker)
  check ((CompilerRuntimeQueries.mutPointerType sparse ty.id).isOk == false) "absent pointer succeeded"
  check ((CompilerRuntimeQueries.mutReferenceType sparse ty.id).isOk == false) "absent reference succeeded"
  check ((CompilerRuntimeQueries.resolveDropGlue sparse ty.id).isOk == false) "absent drop succeeded"
  check ((prepare #[row] none).isOk == false) "legacy omitted constructors accepted"
  let pointerOnly := set row "mut_pointer_type" fact
  let pointer ← must (prepare #[pointerOnly] marker)
  check ((CompilerRuntimeQueries.mutPointerType pointer ty.id) == .ok ty.id) "pointer result changed"
  check ((CompilerRuntimeQueries.mutReferenceType pointer ty.id).isOk == false) "pointer supplied reference"
  let full := set pointerOnly "mut_reference_type" fact
  let legacy ← must (prepare #[full] none)
  check ((CompilerRuntimeQueries.mutReferenceType legacy ty.id) == .ok ty.id) "legacy result changed"
  check ((prepare #[full,full] marker).isOk == false) "duplicate operation row accepted"
  check ((prepare #[full] (some (.str "future"))).isOk == false) "unknown operation schema accepted"
  for key in ["mut_pointer_type", "mut_reference_type"] do
    for bad in [Json.bool true, Json.mkObj [("status", .str "unsupported")],
        Json.mkObj [("status", .str "supported"),
          ("value", Json.mkObj [("type_id", toJson (100000000 : Nat))])]] do
      check ((prepare #[set full key bad] marker).isOk == false) s!"malformed {key} accepted"
  IO.println "runtime operations: sparse failures, exact fields, strict legacy, duplicates and malformed facts PASS"
