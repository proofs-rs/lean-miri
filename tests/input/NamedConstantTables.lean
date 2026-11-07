import Miri.Input.Reader.NamedConstants

open Lean Miri.Input Miri.Input.Reader

private def must (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)
private def reference (id : Nat) : Json := Json.mkObj [("$lean_miri_shared_ref",toJson id)]

private def read (bits : String) : IO (Array NamedConstantQueryData × MIRReader.State) := do
  let definition := Json.mkObj [("crate",toJson (4 : Nat)),("index",toJson (6 : Nat))]
  let value := Json.mkObj [("kind",toJson "scalar"),("bits_unsigned",toJson bits)]
  let query := Json.mkObj [("status",toJson "supported"),
    ("instance_kind",Json.mkObj [("kind",toJson "item"),("def_id",reference 0)]),
    ("generic_args",Json.arr #[]),("type",Json.mkObj [("type_id",toJson (0 : Nat))]),
    ("evaluation",Json.mkObj [("status",toJson "supported"),("value",reference 1)])]
  let row := Json.mkObj [("name",toJson "ANSWER"),("path",reference 2),
    ("typing_env",toJson "fully_monomorphized"),("query",reference 3)]
  let input := Json.mkObj [("shared_payloads",Json.mkObj [("schema_version",toJson (2 : Nat)),
    ("nodes",Json.arr #[definition,value,Json.arr #[toJson "libc",toJson "ANSWER"],query,row])]),
    ("compiler_named_constants",Json.arr #[reference 4])]
  let catalog ← must (Catalog.parse input)
  let (result,state) ← must ((NamedConstantReader.read catalog ⟨1,0,#[some 4]⟩).run
    (MIRReader.initial catalog.nodes.size {}))
  return (← must result,state)

def main : IO Unit := do
  let (rows,state) ← read "42"
  let some row := rows[0]? | throw (IO.userError "named constant row absent")
  let value ← must row.result
  unless row.path == .ok #["libc","ANSWER"] && value.sourceInstance.defId == 0 &&
      value.ty == 0 && value.value == .Scalar (.Int 42 4) &&
      state.compiler.definitions == #[⟨4,6⟩] do
    throw (IO.userError "shared named constant identity or value changed")
  let (rows,state) ← read "4294967296"
  let some row := rows[0]? | throw (IO.userError "failed named constant row absent")
  unless row.result.toOption.isNone && state.compiler.definitions == #[⟨4,6⟩] do
    throw (IO.userError "evaluation failure lost its interned source identity")
