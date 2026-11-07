import MiriTests.Input.ReferenceDecoder
import Miri.MIR.Contents
import Miri.Input.Reader.ReferenceBounds
import Miri.Input.RuntimeMetadata
import Miri.Input.LowerMIR
import MiriTests.Input.LoweringOracle

open Lean Miri Miri.Input

private def must (value : Except ε α) [ToString ε] : IO α :=
  match value with
  | .ok value => pure value
  | .error error => throw (IO.userError (toString error))

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "usage: BodyIDs <export.json>")
  let source ← IO.FS.readFile path
  let catalog ← must (Reader.Catalog.parse (← must (Json.parse source)))
  let decoded ← must (decodeRuntimeJson source)
  let oracle ← must (decodeRuntimeJsonReference source)
  let context := LowerContext.ofDocument decoded.document
  let ctx : Reader.ConstantReader.Context :=
    ⟨decoded.document.types.size, decoded.document.allocations.size, context.scalarSizes⟩
  let mut state := Reader.MIRReader.initial catalog.nodes.size decoded.document.mirTables.compiler
  let mut count := 0
  let mut blocks := 0
  let mut bodyIds := #[]
  for (row, index) in (← must (catalog.array (← must (catalog.field catalog.root "instances" "$")) "instances")).toList.zipIdx do
    let .ok input := catalog.field row "body" "instance" | continue
    let raw ← must (catalog.inspect input "body")
    if raw == .null then continue
    let (id, next) ← must ((Reader.BodyReader.body catalog ctx input s!"instances[{index}].body").run state)
    if let some wireId ← must (catalog.sharedId? input "body") then
      unless id.index == wireId do throw (IO.userError "body wire ID changed")
    let node ← must (next.tables.bodies.lookup id.index)
    let some oracleRow := oracle.document.instances[index]? | throw (IO.userError "instance oracle absent")
    let some expected := oracleRow.body | throw (IO.userError "body oracle absent")
    let lowered ← must (MiriTests.Input.LoweringOracle.lowerBodyUsingTables context expected.toBodyCore state.compiler)
    let observed ← must (MIR.Contents.body {next.tables with regions := next.regions, arguments := next.arguments}
      next.compiler.typeConstants node)
    unless observed == lowered.body do throw (IO.userError "full body instruction semantics changed")
    unless node.locals == lowered.body.locals && node.argumentCount == lowered.body.argumentCount &&
        node.spreadArgument == lowered.body.spreadArgument && node.phase == lowered.body.phase &&
        node.basicBlocks.size == lowered.body.basicBlocks.size do
      throw (IO.userError "body structure changed")
    for (block,index) in node.basicBlocks.toList.zipIdx do
      let block ← must (next.tables.blocks.lookup block.index)
      let some expected := lowered.body.basicBlocks[index]? | throw (IO.userError "block oracle absent")
      unless block.cleanup == expected.cleanup && block.statements.size == expected.statements.size do
        throw (IO.userError "block structure changed")
      let _ ← must (next.tables.terminators.lookup block.terminator.index)
      for statement in block.statements do let _ ← must (next.tables.statements.lookup statement.index); pure ()
    blocks := blocks + node.basicBlocks.size
    state := next
    bodyIds := bodyIds.push id
    count := count + 1
  unless count > 0 do throw (IO.userError "fixture lacks concrete bodies")
  let _ ← must (Reader.ReferenceBounds.validate state bodyIds)
  let some first := bodyIds[0]? | throw (IO.userError "body IDs absent")
  let node ← must (state.tables.bodies.lookup first.index)
  let invalidId := MIR.BodyId.mk state.tables.bodies.size
  let invalid := {state with tables := {state.tables with
    bodies := state.tables.bodies.push (some {node with locals := #[]})}}
  unless !(Reader.ReferenceBounds.validate invalid (bodyIds.push invalidId)).isOk do
    throw (IO.userError "local bound validation leaked between bodies")
  let invalid := {state with tables := {state.tables with
    bodies := state.tables.bodies.push (some {node with sourceScopeCount := 0})}}
  unless !(Reader.ReferenceBounds.validate invalid (bodyIds.push invalidId)).isOk do
    throw (IO.userError "source scope validation leaked between bodies")
  IO.println s!"body IDs: PASS ({count} bodies; {blocks} blocks; typed structure and shared IDs)"
