import Miri.Input.Decoder

open Lean Miri.Input

private def set (value : Json) (key : String) (child : Json) : Except String Json := do
  let fields ← value.getObj?
  pure (Json.mkObj ((key, child) :: fields.toList.filter (fun item => item.1 != key)))

private def malformedCast : Json := Json.mkObj [
  ("kind", toJson ("Cast" : String)),
  ("vtable_allocation", Json.mkObj [
    ("kind", toJson ("dynamic_vtable_upcast" : String))])]

private def must {α : Type} (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected current exporter MIR JSON")
  let base ← must (Json.parse (← IO.FS.readFile path))
  let _ ← must (decodeJson base.compress)
  IO.println "PASS direct-format input accepted before malformed-cast injection"
  let withFirst ← must (set base "synthetic_first" malformedCast)
  let input ← must (set withFirst "synthetic_second" malformedCast)
  match decodeJson input.compress with
  | .error path =>
    check (path == "$.synthetic_first.vtable_allocation: supported dynamic vtable upcast lacks matching compiler cast evidence")
      s!"malformed vtable must retain first DFS diagnostic path; got {path}"
    IO.println s!"PASS malformed vtable first path: {path}"
  | .ok _ => throw (IO.userError "malformed supported dynamic vtable upcast was accepted")
