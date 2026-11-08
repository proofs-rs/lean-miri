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

private partial def probePath? (root node : Json) (path : String := "$") : Option String := do
  if (node.getObjValAs? String "kind").toOption == some "Cast" &&
      ((node.getObjVal? "vtable_allocation").bind (fun d => d.getObjValAs? String "kind")).toOption == some "dynamic_vtable_upcast" then return path
  match node with
  | .obj fields =>
    for (key, child) in fields.toList do
      if let some found := probePath? root child (path ++ "." ++ key) then return found
  | .arr values =>
    for (child, index) in values.toList.zipIdx do
      if let some found := probePath? root child s!"{path}[{index}]" then return found
  | _ => pure ()
  none

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected current exporter MIR JSON")
  let base ← must (Json.parse (← IO.FS.readFile path))
  discard <| must (decodeRuntimeJson base.compress)
  IO.println "PASS direct-format input accepted before malformed-cast injection"
  -- The same exact cast evidence remains valid when its operand uses a
  -- canonical constant ID rather than a place. A different constant type
  -- must still invalidate the exact-pair evidence.
  let some castPath := probePath? base base
    | throw (IO.userError "fixture has no validated vtable probe")
  let some cast := jsonAtPath base castPath
    | throw (IO.userError "validated cast path disappeared")
  let operand ← must (cast.getObjVal? "operand")
  let place ← must (operand.getObjVal? "place")
  let type ← must (place.getObjVal? "type")
  let tables ← must (base.getObjVal? "semantic_tables")
  let constants ← must ((tables.getObjVal? "constants").bind Json.getArr?)
  let constantOperand := Json.mkObj [("kind", toJson ("Constant" : String)),
    ("constant", toJson constants.size)]
  let constantCast ← must (set cast "operand" constantOperand)
  let some sample := constants[0]? | throw (IO.userError "fixture has no canonical constant")
  let sample ← must (set sample "type" type)
  let constants := constants.push sample
  let tables ← must (set tables "constants" (.arr constants))
  let constantInput ← must (set (← must (set base "semantic_tables" tables)) "constant_probe" constantCast)
  discard <| must (decodeJson constantInput.compress)
  discard <| must (decodeRuntimeJson constantInput.compress)
  let types ← must ((base.getObjVal? "types").bind Json.getArr?)
  let originalType ← must type.getNat?
  let some differentType := types.find? (fun row =>
      (row.getObjValAs? Nat "type_id").toOption != some originalType) |
    throw (IO.userError "fixture has no different valid compiler type")
  let differentType ← must (differentType.getObjVal? "type_id")
  let constants := constants.set! (constants.size - 1) (← must (set sample "type" differentType))
  let wrongTables ← must (set tables "constants" (.arr constants))
  let wrongInput ← must (set constantInput "semantic_tables" wrongTables)
  let expected := "$.constant_probe.vtable_allocation: supported dynamic vtable upcast lacks matching compiler cast evidence"
  match decodeJson wrongInput.compress, decodeRuntimeJson wrongInput.compress with
  | .error a, .error b =>
    check (a == expected && b == expected)
      s!"wrong valid canonical type must fail exact evidence matching: {a} / {b}"
  | _, _ => throw (IO.userError "wrong canonical constant type passed exact probe evidence")
  IO.println "PASS exact vtable probe resolves canonical constant type"
  -- MIR rvalues retain occurrence identity and stay inline in schema 4.
  -- Repeated equal source records must still report the first DFS occurrence.
  let withFirst ← must (set base "synthetic_first" malformedCast)
  let input ← must (set withFirst "synthetic_second" malformedCast)
  match decodeJson input.compress, decodeRuntimeJson input.compress with
  | .error fullPath, .error path =>
    check (fullPath == path) "full/runtime first DFS diagnostics differ"
    check (path == "$.synthetic_first.vtable_allocation: supported dynamic vtable upcast lacks matching compiler cast evidence")
      s!"repeated MIR malformed vtable must retain first DFS diagnostic path; got {path}"
    IO.println s!"PASS repeated MIR malformed vtable first path: {path}"
  | _, _ => throw (IO.userError "malformed supported dynamic vtable upcast was accepted")
