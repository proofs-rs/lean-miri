import Miri.Frontend.FoundationEntrySeed
import Miri.Input.SourceCompilerBodies
open Lean Miri Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)

def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected genuine std foundation source")
  let document ← checked (decode (← checked (Json.parse (← IO.FS.readFile path))))
  let initial ← checked (compilerEntrySeed document)
  let mut world := initial
  for node in initial.canonical.instances do
    let (updated,_) ← checked (Input.SourceCompilerBodies.demandLoadedBody world node.id)
    world := updated
  unless world.canonical.bodies.size == initial.canonical.instances.size do
    throw (IO.userError "requested source body not installed")
  let mut aggregates := 0
  let mut references := 0
  let mut unsizes := 0
  let mut calls := 0
  let mut projected := 0
  for body in world.canonical.bodies do
    for block in body.mir.basicBlocks do
      for statement in block.statements do
        match statement.kind with
        | .Assign _ (.Aggregate (.Closure ..) _) => aggregates := aggregates + 1
        | .Assign _ (.Ref ..) => references := references + 1
        | .Assign _ (.Cast (.PointerCoercion .Unsize _) _ _) => unsizes := unsizes + 1
        | _ => pure ()
      if let .Call .. := block.terminator.kind then calls := calls + 1
    for facts in body.nodeFacts do
      for fact in facts do
        for place in fact.places do
          unless place.projectionTypes.size == place.place.projection.size do
            throw (IO.userError "projected-place facts incomplete")
          if !place.place.projection.isEmpty then projected := projected + 1
  unless aggregates > 0 && references > 0 && unsizes > 0 && calls > 0 && projected > 0 do
    throw (IO.userError "genuine std constructor domain not exercised")
  let some material := initial.canonical.sourceMaterial | throw (IO.userError "typed material absent")
  let some mir := material.genericMir | throw (IO.userError "typed MIR absent")
  let some physical := material.physical | throw (IO.userError "typed types absent")
  let hasClosure := fun body : Input.SourceMir.Body => body.blocks.any fun block => block.statements.any fun statement =>
    match statement.kind with | .assign _ (.aggregateClosure ..) => true | _ => false
  let some selected := mir.bodies.find? hasClosure | throw (IO.userError "closure aggregate source absent")
  let some owner := initial.canonical.instances.find? (fun node =>
    node.definitionId.bind (initial.canonical.definitions[·]?) == some selected.definition)
    | throw (IO.userError "selected source owner instance absent")
  let some wrong := physical.definitions.findIdx? (fun definition => definition.kind == "fn" && definition.raw != selected.definition)
    | throw (IO.userError "nonclosure source declaration absent")
  let changed := {mir with bodies := mir.bodies.map fun body =>
    {body with blocks := body.blocks.map fun block =>
      {block with statements := block.statements.map fun statement =>
        match statement.kind with
        | .assign destination (.aggregateClosure _ args values) =>
          {statement with kind := .assign destination (.aggregateClosure wrong args values)}
        | _ => statement}}}
  let broken := {initial with canonical := {initial.canonical with sourceMaterial := some {material with genericMir := some changed}}}
  match Input.SourceCompilerBodies.demandLoadedBody broken owner.id with
  | .ok _ => throw (IO.userError "closure declaration contradiction accepted")
  | .error error => unless error.startsWith "Invalid source closure aggregate" do
      throw (IO.userError s!"unexpected closure identity rejection: {error}")
  IO.println s!"typed std selected-body demands: {aggregates} closure aggregate, {references} refs, {unsizes} unsize, {calls} calls, {projected} projected places; no winner/allocation constructed"
