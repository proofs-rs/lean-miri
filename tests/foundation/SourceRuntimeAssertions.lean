import Miri.Frontend.FoundationSourceMaterial
import Miri.Frontend.FoundationSession
open Lean Miri Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α := match value with
  | .ok value => pure value | .error error => throw (IO.userError error)
private def parse (path : String) : IO Input.SourceMir.Material := do
  let json ← checked (Json.parse (← IO.FS.readFile path))
  let document ← checked (decode json)
  let physical ← checked (SourceTypesParser.material json)
  SourceMirParser.material document (some physical) |> checked
private def messageTag : Input.SourceMir.AssertKind → String
  | .boundsCheck .. => "bounds_check" | .overflow .. => "overflow"
  | .overflowNeg .. => "overflow_neg" | .divisionByZero .. => "division_by_zero"
  | .remainderByZero .. => "remainder_by_zero" | _ => "unexpected"
private def operandPreserved (actual : Input.SourceMir.Operand) (original : Json) : IO Unit := do
  let tag ← checked (original.getObjValAs? String "kind")
  match actual with
  | .copy place | .move place =>
    unless tag == (match actual with | .copy _ => "copy" | _ => "move") do throw (IO.userError "operand copy/move changed")
    let raw ← checked (original.getObjVal? "place")
    let projection ← checked (raw.getObjValAs? (Array Json) "projection")
    unless place.localId == (← checked (raw.getObjValAs? Nat "local")) && place.projection.size == projection.size do
      throw (IO.userError "operand place changed")
    for step in place.projection, rawStep in projection do
      let .field index type := step | throw (IO.userError "unexpected fixture projection")
      unless index == (← checked (rawStep.getObjValAs? Nat "index")) && type == (← checked (rawStep.getObjValAs? Nat "type")) do
        throw (IO.userError "assert operand projection changed")
  | .constant value =>
    let .typeConstant (.value type bits bytes) := value.value | throw (IO.userError "unexpected fixture constant")
    let raw ← checked (original.getObjVal? "value")
    unless tag == "constant" && value.type == (← checked (original.getObjValAs? Nat "type")) &&
        type == (← checked (raw.getObjValAs? Nat "type")) &&
        toString bits == (← checked (raw.getObjValAs? String "bits")) &&
        bytes == (← checked (raw.getObjValAs? Nat "size_bytes")) do throw (IO.userError "assert constant changed")
  | _ => throw (IO.userError "unexpected fixture operand")
def main (paths : List String) : IO Unit := do
  let [runtimePath,assertPath] := paths | throw (IO.userError "expected genuine runtime-check and assert inputs")
  let runtime ← parse runtimePath
  let mut checks : Array MIR.RuntimeChecks := #[]
  for body in runtime.bodies do
    for block in body.blocks do
      for statement in block.statements do
        if let .assign _ (.use (.runtimeChecks kind _) _) := statement.kind then checks := checks.push kind
  unless checks.size == 2 && checks.contains .UbChecks && checks.contains .OverflowChecks do
    throw (IO.userError "genuine runtime-check operands not retained")
  let assertions ← parse assertPath
  let raw ← checked (Json.parse (← IO.FS.readFile assertPath))
  let rawBodies ← checked (raw.getObjValAs? (Array Json) "bodies")
  let mut kinds : Array String := #[]
  for body in assertions.bodies, rawBody in rawBodies do
    for block in body.blocks, rawBlock in (← checked (rawBody.getObjValAs? (Array Json) "blocks")) do
      let original ← checked (rawBlock.getObjVal? "terminator")
      unless (← checked (original.getObjValAs? String "kind")) == "assert" do continue
      let .assert condition expected message target unwind := block.terminator.kind
        | throw (IO.userError "genuine assert terminator lost")
      unless expected == (← checked (original.getObjValAs? Bool "expected")) &&
          target == (← checked (original.getObjValAs? Nat "target")) do
        throw (IO.userError "assert expected/target changed")
      let originalMessage ← checked (original.getObjVal? "message")
      let tag ← checked (originalMessage.getObjValAs? String "kind")
      unless messageTag message == tag do throw (IO.userError "assert kind changed")
      operandPreserved condition (← checked (original.getObjVal? "condition"))
      unless unwind == .continueUnwind do throw (IO.userError "genuine assert unwind changed")
      match message with
      | .boundsCheck length index =>
        operandPreserved length (← checked (originalMessage.getObjVal? "length"))
        operandPreserved index (← checked (originalMessage.getObjVal? "index"))
      | .overflow _ left right =>
        operandPreserved left (← checked (originalMessage.getObjVal? "left"))
        operandPreserved right (← checked (originalMessage.getObjVal? "right"))
      | .overflowNeg value | .divisionByZero value | .remainderByZero value =>
        operandPreserved value (← checked (originalMessage.getObjVal? "operand"))
      | _ => throw (IO.userError "unexpected fixture assertion")
      kinds := kinds.push tag
  unless kinds.size == 5 && #["bounds_check","overflow","overflow_neg","division_by_zero","remainder_by_zero"].all kinds.contains do
    throw (IO.userError "genuine assert coverage incomplete")
  IO.println "genuine RuntimeChecks and five Assert constructors retained PASS"
