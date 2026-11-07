import Miri.Input.Reader.NamedGlobals

open Lean Miri.Input Miri.Input.Reader

private def must (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def read (rows : String) : IO (Except String (Array NamedGlobalQueryData) × MIRReader.State) := do
  let catalog ← must (Catalog.parse (← must (Json.parse rows)))
  must ((NamedGlobalReader.read catalog 1 1).run (MIRReader.initial catalog.nodes.size {}))

def main : IO Unit := do
  let (.ok rows,state) ← read "{\"shared_payloads\":{\"schema_version\":2,\"nodes\":[{\"crate\":3,\"index\":4},[\"libc\",\"VALUE\"],{\"definition\":{\"$lean_miri_shared_ref\":0},\"kind\":\"static\",\"type\":{\"type_id\":0},\"allocation\":{\"allocation_id\":0}},{\"status\":\"supported\",\"value\":{\"$lean_miri_shared_ref\":2}},{\"name\":\"VALUE\",\"path\":{\"$lean_miri_shared_ref\":1},\"typing_env\":\"fully_monomorphized\",\"query\":{\"$lean_miri_shared_ref\":3}},[{\"$lean_miri_shared_ref\":4}]]},\"compiler_named_statics\":{\"$lean_miri_shared_ref\":5}}"
    | throw (IO.userError "shared named globals rejected")
  let some row := rows[0]? | throw (IO.userError "named global row missing")
  unless row.name == "VALUE" && row.result == .ok ⟨0,0,0,true⟩ &&
      state.compiler.definitions == #[⟨3,4⟩] do
    throw (IO.userError "named global typed identity changed")
  let (.ok rows,state) ← read "{\"shared_payloads\":{\"schema_version\":2,\"nodes\":[]},\"compiler_named_statics\":[{\"name\":\"VALUE\",\"path\":[\"libc\",\"VALUE\"],\"typing_env\":\"fully_monomorphized\",\"query\":{\"status\":\"supported\",\"value\":{\"definition\":{\"crate\":3,\"index\":4},\"kind\":\"static\",\"type\":{\"type_id\":1},\"allocation\":{\"allocation_id\":0}}}}]}"
    | throw (IO.userError "failed named global query should remain a row")
  let some row := rows[0]? | throw (IO.userError "failed named global row missing")
  unless row.result.toOption.isNone && state.compiler.definitions.isEmpty do
    throw (IO.userError "failed named global query changed definition table")
  let (.error _,_) ← read "{\"shared_payloads\":{\"schema_version\":2,\"nodes\":[]},\"compiler_named_statics\":[{\"name\":\"VALUE\",\"path\":[\"other\",\"VALUE\"],\"typing_env\":\"fully_monomorphized\"}]}"
    | throw (IO.userError "inexact named global path accepted")
