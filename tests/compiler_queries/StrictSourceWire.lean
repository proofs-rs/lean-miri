import Miri.Input.Decoder

/-! Old source execution wires cannot enter the strict rustc-result document. -/
open Lean Miri.Input
private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)
private def rejects (value : Json) (message : String) : IO Unit := do
  match decodeJson value.compress with
  | .ok _ => throw (IO.userError s!"accepted old source wire: {message}")
  | .error _ => pure ()

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected fresh rustc export")
  let input ← must (Json.parse (← IO.FS.readFile path))
  let _ ← must (decodeJson input.compress)
  for (key,message) in [
      ("mir_templates","mir_templates"),
      ("ctfe_scalar_sources","ctfe_scalar_sources")] do
    rejects (input.setObjVal! key (toJson #[Json.mkObj []])) message
  let bodies ← must ((← must (input.getObjVal? "bodies")).getArr?)
  let some first := bodies[0]? | throw (IO.userError "fixture has no body")
  for (kind,message) in [
      ("copy_template","source MIR template body"),
      ("fn_pointer_shim","source FnPtr shim body")] do
    let legacy := first.setObjVal! "body_kind" (toJson kind)
    rejects (input.setObjVal! "bodies" (toJson (bodies.set! 0 legacy))) message
  IO.println "PASS old source execution wires reject"
