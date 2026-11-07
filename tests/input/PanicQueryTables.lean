import Miri.Input.Reader.PanicQueries

open Lean Miri.Input Miri.Input.Reader

private def must (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def read (text : String) : IO (Option (Except String (Array PanicQueryData)) × MIRReader.State) := do
  let catalog ← must (Catalog.parse (← must (Json.parse text)))
  must ((PanicQueryReader.read catalog).run (MIRReader.initial catalog.nodes.size {}))

def main : IO Unit := do
  let (some (.ok rows),state) ← read "{\"shared_payloads\":{\"schema_version\":2,\"nodes\":[{\"crate\":9,\"index\":11},[\"lifetime\"],{\"lang_item\":\"Panic\",\"status\":\"supported\",\"definition\":{\"$lean_miri_shared_ref\":0},\"generic_parameters\":{\"$lean_miri_shared_ref\":1}},[{\"$lean_miri_shared_ref\":2}]]},\"compiler_panic_queries\":{\"$lean_miri_shared_ref\":3}}"
    | throw (IO.userError "shared panic catalog rejected")
  let some row := rows[0]? | throw (IO.userError "panic row missing")
  unless rows.size == 1 && row.definition == .ok (some 0) &&
      row.genericParameters == .ok #[.lifetime] &&
      state.compiler.definitions == #[⟨9,11⟩] do
    throw (IO.userError "panic typed definition or generic parameters changed")
  let (none,_) ← read "{\"shared_payloads\":{\"schema_version\":2,\"nodes\":[]}}"
    | throw (IO.userError "absent catalog was demanded")
  let (some (.ok rows),_) ← read "{\"shared_payloads\":{\"schema_version\":2,\"nodes\":[]},\"compiler_panic_queries\":[{\"lang_item\":\"Panic\",\"status\":\"unavailable\"}]}"
    | throw (IO.userError "unresolved row must be retained")
  let some row := rows[0]? | throw (IO.userError "unresolved panic row missing")
  unless row.definition.toOption.isNone do throw (IO.userError "unresolved panic definition accepted")
  let (some (.error _),_) ← read "{\"shared_payloads\":{\"schema_version\":2,\"nodes\":[]},\"compiler_panic_queries\":[{\"lang_item\":\"Panic\",\"status\":\"unavailable\"},{\"lang_item\":\"Panic\",\"status\":\"unavailable\"}]}"
    | throw (IO.userError "duplicate panic tag accepted")
