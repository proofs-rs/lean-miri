import Miri.Input.Decoder

open Lean Miri.Input

private def must (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw (IO.userError message)

private def set (value : Json) (key : String) (child : Json) : Except String Json := do
  let fields ← value.getObj?
  pure (Json.mkObj ((key, child) :: fields.toList.filter (·.1 != key)))

private def reject (input : Json) (label : String) : IO Unit := do
  for outcome in #[decodeJson input.compress |>.map (fun _ => ())] do
    if outcome.isOk then throw (IO.userError s!"{label}: incomplete selected key evidence accepted")

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected prepared selected-keys JSON")
  let input ← must (Json.parse (← IO.FS.readFile path))
  discard <| must (decodeJson input.compress)
  discard <| must (decodeJson input.compress)
  let world ← must (input.getObjVal? "compiler_alloc_id_world")
  let rows ← must ((← must (world.getObjVal? "dedup_catalog")).getArr?)
  for family in #["function", "vtable"] do
    let selected := rows.filter fun row => (row.getObjValAs? String "key_kind").toOption == some family
    if selected.isEmpty then throw (IO.userError s!"fixture has no {family} key")
    let omitted := rows.filter fun row => (row.getObjValAs? String "key_kind").toOption != some family
    let missing ← must (set world "dedup_catalog" (.arr omitted))
    reject (← must (set input "compiler_alloc_id_world" missing)) s!"missing {family} key"
    let mut shortened := #[]
    for row in rows do
      if (row.getObjValAs? String "key_kind").toOption == some family then
        let salts ← must ((← must (row.getObjVal? "salts")).getArr?)
        shortened := shortened.push (← must (set row "salts" (.arr (salts.extract 0 1))))
      else shortened := shortened.push row
    let incomplete ← must (set world "dedup_catalog" (.arr shortened))
    reject (← must (set input "compiler_alloc_id_world" incomplete)) s!"incomplete {family} salts"
  IO.println "SelectedKeyCoverageStrict: selected function/vtable keys and all salts required at every input boundary"
