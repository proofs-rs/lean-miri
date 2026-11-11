import Miri.Input.Decoder

open Lean Miri.Input

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private partial def oldLockstep (input : Json) : Except String Json := do
  match input with
  | .obj fields =>
    let fields ← fields.toList.mapM fun (key, child) => do
      pure (key, ← oldLockstep child)
    if (input.getObjValAs? String "query_kind").toOption == some "lockstep_tails" then
      let tails := fields.filter fun (key, _) => key == "source_tail" || key == "target_tail"
      return Json.mkObj (("value", Json.mkObj tails) :: fields.filter (fun (key, _) =>
        key != "source_tail" && key != "target_tail"))
    return Json.mkObj fields
  | .arr items => return .arr (← items.mapM oldLockstep)
  | scalar => return scalar

def main (args : List String) : IO Unit := do
  let (path, requireUpcast) ← match args with
    | [path] => pure (path, true)
    | [path, "no-upcast"] => pure (path, false)
    | _ => throw (IO.userError "expected fresh exporter input and optional no-upcast control")
  let input ← match Json.parse (← IO.FS.readFile path) with
    | .ok input => pure input
    | .error error => throw (IO.userError error)
  match decodeJson input.compress with
  | .ok _ => IO.println "PASS direct compiler input accepted"
  | .error error => throw (IO.userError error)
  let wrapped ← match oldLockstep input with
    | .ok wrapped => pure wrapped
    | .error error => throw (IO.userError error)
  if !requireUpcast then
    check (wrapped == input) "no-upcast control unexpectedly contains lockstep query answers"
    IO.println "PASS direct input without lockstep upcast answers accepted"
    return
  check (wrapped != input) "fixture must contain lockstep query answers"
  match decodeJson wrapped.compress with
  | .error error =>
    check (error.endsWith "obsolete wrapped compiler cast query value")
      s!"expected exact upcast-evidence rejection, got {error}"
    IO.println "PASS obsolete wrapped lockstep evidence rejected"
  | .ok _ => throw (IO.userError "fixture must exercise dynamic-upcast evidence validation")
