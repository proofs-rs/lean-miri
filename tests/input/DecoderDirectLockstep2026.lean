import Miri.Input.Decoder

open Lean Miri.Input

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

-- Reintroduce the removed success envelope only for lockstep query answers.
-- Keep the exact query keys and all referenced type identities unchanged.
private def oldLockstep (input : Json) : Except String Json := do
  let nodes ← (← input.getObjVal? "compiler_cast_queries").getArr?
  let nodes ← nodes.mapM fun raw => do
    if (raw.getObjValAs? String "query_kind").toOption != some "lockstep_tails" then
      return raw
    let fields := (← raw.getObj?).toList
    let tails := fields.filter fun (key, _) => key == "source_tail" || key == "target_tail"
    return Json.mkObj (("value", Json.mkObj tails) :: fields.filter (fun (key, _) =>
      key != "source_tail" && key != "target_tail"))
  let fields := (← input.getObj?).toList
  return Json.mkObj (("compiler_cast_queries", .arr nodes) ::
    fields.filter (fun (key, _) => key != "compiler_cast_queries"))

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected fresh dynamic-vtable-upcast exporter input")
  let input ← match Json.parse (← IO.FS.readFile path) with
    | .ok input => pure input
    | .error error => throw (IO.userError error)
  match decodeRuntimeJson input.compress with
  | .ok _ => IO.println "PASS direct lockstep upcast evidence accepted"
  | .error error => throw (IO.userError error)
  let wrapped ← match oldLockstep input with
    | .ok wrapped => pure wrapped
    | .error error => throw (IO.userError error)
  check (wrapped != input) "fixture must contain lockstep query answers"
  match decodeRuntimeJson wrapped.compress with
  | .error error =>
    check (error.endsWith "supported dynamic vtable upcast lacks matching compiler cast evidence")
      s!"expected exact upcast-evidence rejection, got {error}"
    IO.println "PASS obsolete wrapped lockstep evidence rejected"
  | .ok _ => throw (IO.userError "fixture must exercise dynamic-upcast evidence validation")
