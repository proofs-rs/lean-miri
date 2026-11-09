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
  let [path] := args | throw (IO.userError "expected fresh dynamic-vtable-upcast exporter input")
  let input ← match Json.parse (← IO.FS.readFile path) with
    | .ok input => pure input
    | .error error => throw (IO.userError error)
  match decodeJson input.compress with
  | .ok _ => IO.println "PASS direct lockstep upcast evidence accepted"
  | .error error => throw (IO.userError error)
  let wrapped ← match oldLockstep input with
    | .ok wrapped => pure wrapped
    | .error error => throw (IO.userError error)
  check (wrapped != input) "fixture must contain lockstep query answers"
  match decodeJson wrapped.compress with
  | .error error =>
    check (error.endsWith "supported dynamic vtable upcast lacks matching compiler cast evidence")
      s!"expected exact upcast-evidence rejection, got {error}"
    IO.println "PASS obsolete wrapped lockstep evidence rejected"
  | .ok _ => throw (IO.userError "fixture must exercise dynamic-upcast evidence validation")
