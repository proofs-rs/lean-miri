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
  -- Unknown extension fields are skipped, even when their names or contents
  -- resemble MIR. Validation applies to the schema's actual typed nodes.
  let withFirst ← must (set base "synthetic_first" malformedCast)
  let extensions ← must (set withFirst "synthetic_second" malformedCast)
  let _ ← must (decodeJson extensions.compress)
  IO.println "PASS unknown Cast-shaped extension payloads skipped"
  let bodies ← must ((← must (base.getObjVal? "bodies")).getArr?)
  let some body := bodies[0]? | throw (IO.userError "fixture has no body")
  let blocks ← must ((← must (body.getObjVal? "basic_blocks")).getArr?)
  let some block := blocks[0]? | throw (IO.userError "fixture has no block")
  let locals ← must ((← must (body.getObjVal? "locals")).getArr?)
  let some localDecl := locals[0]? | throw (IO.userError "fixture has no local")
  let ty ← must (localDecl.getObjVal? "type")
  let terminator ← must (block.getObjVal? "terminator")
  let sourceInfo ← must (terminator.getObjVal? "source_info")
  let place := Json.mkObj [("local", toJson (0 : Nat)), ("type", ty), ("projection", toJson (#[] : Array Json))]
  let cast ← must (set malformedCast "cast_kind" (Json.mkObj [
    ("kind", toJson ("PointerCoercion" : String)),
    ("coercion", Json.mkObj [("kind", toJson ("Unsize" : String))]),
    ("source", toJson ("as_cast" : String))]))
  let cast ← must (set cast "operand" (Json.mkObj [("kind", toJson ("Copy" : String)), ("place", place)]))
  let cast ← must (set cast "target_type" ty)
  let statement := Json.mkObj [("source_info", sourceInfo), ("kind", Json.mkObj [
    ("variant", toJson ("Assign" : String)), ("place", place), ("rvalue", cast)])]
  let block ← must (set block "statements" (toJson #[statement]))
  let body ← must (set body "basic_blocks" (toJson (blocks.set! 0 block)))
  let input ← must (set base "bodies" (toJson (bodies.set! 0 body)))
  match decodeJson input.compress with
  | .error message =>
    check (message.contains "runtime_vtable")
      s!"malformed typed vtable must fail its missing metadata; got {message}"
    IO.println s!"PASS malformed typed vtable payload rejected: {message}"
  | .ok _ => throw (IO.userError "malformed typed dynamic vtable upcast was accepted")
