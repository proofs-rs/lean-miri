import Miri.Input.Reader.MainQueries

open Lean Miri.Input Miri.Input.Reader

private def must (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)
private def reference (id : Nat) : Json := Json.mkObj [("$lean_miri_shared_ref",toJson id)]
private def supported (value : Json) : Json := Json.mkObj [("status",toJson "supported"),("value",value)]

private def read (withEntryType : Bool) : IO (MainQueryData × MIRReader.State) := do
  let definition := Json.mkObj [("crate",toJson (0 : Nat)),("index",toJson (7 : Nat))]
  let start := Json.mkObj [("crate",toJson (0 : Nat)),("index",toJson (9 : Nat))]
  let ty := Json.mkObj [("type_id",toJson (0 : Nat))]
  let signature := supported (Json.mkObj [("has_bound_variables",toJson false),
    ("output_has_bound_variables",toJson false),("return_type",ty),("function_pointer_type",ty),
    ("compiler_selected_entry",toJson true),("start_resolution",supported .null)])
  let entry := Json.mkObj [("definition",reference 0),("generic_parameters",Json.arr #[]),("signature_query",reference 2)]
  let fields := [("typing_env",toJson "fully_monomorphized"),("start_lang_item",reference 1),
    ("compiler_entry",reference 0),("entries",Json.arr #[reference 3]),
    ("link_sections",Json.mkObj [("status",toJson "unsupported")])]
  let fields := if withEntryType then ("compiler_entry_type",supported (Json.mkObj [
    ("definition",reference 0),("kind",toJson "rustc_main"),("sigpipe",toJson (255 : Nat))])) :: fields else fields
  let input := Json.mkObj [("shared_payloads",Json.mkObj [("schema_version",toJson (2 : Nat)),
    ("nodes",Json.arr #[definition,start,signature,entry])]),("compiler_main_queries",Json.mkObj fields)]
  let catalog ← must (Catalog.parse input)
  let (result,state) ← must ((MainQueryReader.read catalog 1 0).run (MIRReader.initial catalog.nodes.size {}))
  return (← must result,state)

def main : IO Unit := do
  let (data,state) ← read true
  let some entry := data.entries[0]? | throw (IO.userError "main entry missing")
  unless data.start == some 0 && data.compilerEntry == some 1 &&
      data.compilerEntryType == .ok (some (1,255)) && entry.definition == 1 &&
      entry.start == .ok none && entry.signature.isOk && data.sections.toOption.isNone &&
      state.compiler.definitions == #[⟨0,9⟩,⟨0,7⟩] do
    throw (IO.userError "shared main metadata changed")
  let (data,_) ← read false
  unless data.compilerEntryType.toOption.isNone && data.entries.size == 1 do
    throw (IO.userError "missing EntryFnType failure was not deferred")
