import Miri.Frontend.FoundationSourceMir
open Lean Miri Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)

def main (paths : List String) : IO Unit := do
  for path in paths do
    let document ← checked (decode (← checked (Json.parse (← IO.FS.readFile path))))
    let source ← checked (SourceMirParser.material document)
    unless source.bodies.size ≥ document.bodies.size do throw (IO.userError "typed MIR lost source bodies")
    for (raw,body) in document.bodies.zip source.bodies do
      unless body.locals.size == (← checked (raw.getObjValAs? (Array Nat) "locals")).size &&
          body.blocks.size == (← checked (raw.getObjValAs? (Array Json) "blocks")).size do
        throw (IO.userError "typed MIR body shape differs")
    let some first := document.bodies[0]? | throw (IO.userError "body absent")
    let localTypes ← checked (first.getObjValAs? (Array Nat) "locals")
    let invalid := first.setObjVal! "locals" (toJson (localTypes.mapIdx fun index ty => if index == 0 then document.types.size else ty))
    match SourceMirParser.material {document with bodies := #[invalid]} with
    | .error error => unless error.startsWith "Invalid typed source MIR:" do throw (IO.userError "malformed reference not Invalid")
    | .ok _ => throw (IO.userError "out-of-bounds source type accepted")
    let blocks ← checked (first.getObjValAs? (Array Json) "blocks")
    let future := first.setObjVal! "blocks" (toJson (blocks.mapIdx fun index block =>
      if index == 0 then block.setObjVal! "terminator" (Json.mkObj [("kind",toJson "future_terminator")]) else block))
    let retained ← checked (SourceMirParser.body document future)
    let some block := retained.blocks[0]? | throw (IO.userError "typed block absent")
    unless block.terminator.kind == .unsupported "future_terminator" do
      throw (IO.userError "unknown syntax did not retain unsupported tag")
    IO.println s!"typed MIR {path}: {source.bodies.size} source bodies retained"
