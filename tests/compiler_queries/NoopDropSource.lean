import Miri.Input.Decoder

/-! Genuine exported no-op shim source; metadata stays syntactic and the body
is reconstructed on demand in the retained execution type universe. -/
open Miri.Input
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def checked (document : ImportDocument) : Except String Nat := do
  let mut world ← TypeArena.World.ofDocument document
  let mut count := 0
  for (seed,index) in document.bodies.zipIdx do
    let .noopDrop reference := seed | continue
    let metadata ← SourceMir.metadata document index
    unless metadata.callSites.isEmpty && metadata.requiredConsts.isEmpty &&
        metadata.localSources.size == 2 && metadata.sourceScopes.size == 1 do
      throw "no-op drop metadata retained executable query answers"
    let some sourceInstance := document.instances[reference.instanceId]?
      | throw "no-op drop instance absent"
    let #[.Type element] := sourceInstance.genericArgs | throw "fixture no-op drop argument missing"
    let (body,retained) ← (SourceMir.resolveBody document index).run world
    unless body.mir.argumentCount == 1 && body.mir.locals.size == 2 &&
        body.mir.basicBlocks.size == 1 && body.mir.spreadArgument.isNone do
      throw "no-op drop body constructor shape changed"
    let some block := body.mir.basicBlocks[0]? | throw "no-op drop return block absent"
    unless block.statements.isEmpty && !block.cleanup && block.terminator.kind == .Return &&
        block.terminator.sourceInfo == ⟨⟨reference.sourceSpan.spanId⟩,0⟩ do
      throw "no-op drop terminator/source identity changed"
    let output ← retained.lookupType body.mir.locals[0]!
    let outputIsUnit := match output with
      | .material node => match node.shape with | .tuple fields => fields.isEmpty | _ => false
      | .constructed (.tuple fields) => fields.isEmpty
      | _ => false
    unless outputIsUnit do throw "no-op drop return local is not unit"
    let input ← retained.lookupType body.mir.locals[1]!
    let inputIsErasedMutRef : Bool := match input with
      | .material node => match node.shape with
        | .reference child .Mut .Erased => child == element
        | _ => false
      | .constructed key => key == .reference element .Mut .Erased
    unless inputIsErasedMutRef do throw "signature region binder was not instantiated with erased"
    let (again,reused) ← (SourceMir.resolveBody document index).run retained
    unless again.mir == body.mir && reused.typeCount == retained.typeCount do
      throw "no-op drop body resolution duplicated constructor identities"
    let .Shim (.DropGlue definition none) := sourceInstance.instanceKind | throw "fixture shim kind"
    let wrongKind := {sourceInstance with instanceKind := .Shim (.DropGlue definition (some element))}
    let corrupted := {document with instances := document.instances.set! reference.instanceId wrongKind}
    unless (SourceMir.metadata corrupted index).toOption.isNone do
      throw "nontrivial drop glue accepted by no-op source category"
    world := reused
    count := count + 1
  unless count > 0 do throw "fixture contained no no-op drop source seeds"
  pure count

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected strict no-op drop source export")
  let document := (← must (decodeJson (← IO.FS.readFile path))).document
  let count ← must (checked document)
  IO.println s!"PASS {count} actual no-op drop source bodies; same-world identity reuse and nontrivial-drop rejection"
