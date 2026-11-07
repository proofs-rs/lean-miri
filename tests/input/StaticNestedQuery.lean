import Miri.Input.DecoderValues

open Lean Miri.Input

private def must (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)
private def ref (id : Nat) : Json := Json.mkObj [("$lean_miri_shared_ref",toJson id)]
private def source (nested : Option Json) : Json := Json.mkObj ([
  ("status",toJson "supported"),("size_bytes",toJson (0 : Nat)),("align_bytes",toJson (1 : Nat)),
  ("mutability",toJson "immutable"),("is_static",toJson true),
  ("is_foreign_item",toJson false),("thread_local",toJson false)] ++ nested.toList.map ("nested",·))

def main : IO Unit := do
  let catalog ← must (Reader.Catalog.parse (Json.mkObj [
    ("shared_payloads",Json.mkObj [("schema_version",toJson (2 : Nat)),
      ("nodes",.arr #[toJson true,source (some (ref 0))])])]))
  let _ : Reader.JsonFields := catalog.jsonFields
  let info ← must (decodeStaticGlobalInfo (ref 1))
  unless info.nested == .ok true do throw (IO.userError "shared nested-static query changed")
  for value in #[source none,source (some (toJson "unknown"))] do
    let info ← must (decodeStaticGlobalInfo value)
    unless !info.nested.isOk do throw (IO.userError "missing/invalid nested-static query was synthesized")
  IO.println "nested-static typed query: PASS"
