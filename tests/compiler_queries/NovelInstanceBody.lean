import Miri.Input.Decoder
import Miri.Input.SourceMirCall
import Miri.Input.CallResolution

/-! Body-provider demand with truncated material namespaces. Raw body syntax
is instantiated through execution-owned identities; ABI is tested separately. -/
open Miri.Input
private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)
private def liftPure (result : Except String α) : RuntimeArrayTypes.CompilerM α :=
  match result with | .ok value => pure value | .error error => throw error

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected fresh source-call fixture")
  let document := (← must (decodeJson (← IO.FS.readFile path))).document
  let metadata ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let initial ← must ((RuntimeArrayTypes.create metadata).mapError (fun error => reprStr error))
  let store ← must (InstanceArena.Store.ofSource initial.arena (document.instances.extract 0 3))
  let initial := {initial with instances := store, bodies := BodyArena.Store.ofSource #[]}
  let some oracle := document.instances[4]? | throw (IO.userError "leaf<u64> oracle absent")
  let expected ← must (InstanceArena.Key.ofSource initial.arena oracle.instanceKind oracle.genericArgs)
  let some bodyIndex := document.bodies.findIdx? (·.instanceId == 2)
    | throw (IO.userError "relay<u64> raw source absent")
  let some seed ← must (SourceMirCall.source document bodyIndex 0)
    | throw (IO.userError "relay raw call absent")
  let resolve := SourceMirCall.resolveWith
    (fun args => do liftPure (GenericInstantiationWorld.ofArguments (← get).arena 16384 args))
    (fun identity => do liftPure ((← get).arena.definitionRef identity))
    (fun term => RuntimeArrayTypes.liftType (GenericInstantiationWorld.resolveType 16384 term))
    CompilerInstance.item seed
  let ((callee,_),world) ← must (resolve.run initial)
  unless callee.instanceId == 3 do throw (IO.userError "instance did not append densely")
  unless (← must (CompilerInstance.source world callee.instanceId)) == expected do
    throw (IO.userError "constructed callee differs from independent rustc full instance key")
  let program ← must (lowerProgram document)
  let prepared ← must (CallResolution.prepareWithRuntime metadata program)
  let (loaded,retained) ← must ((CallResolution.loadedBodyOfInstance prepared callee.instanceId).run world)
  unless loaded.identity.index == 0 && retained.bodies.constructed.size == 1 do
    throw (IO.userError "constructed body did not append in its own dense namespace")
  let (body,retained) ← must ((program.resolveBodyIdentity loaded.identity).run retained)
  unless body.input.instanceId == callee.instanceId && body.input.definitionId == some expected.kind.defId do
    throw (IO.userError "raw body demand lost complete instance ownership")
  let some (Miri.MIR.GenericArg.Type argument) := expected.arguments[0]? | throw (IO.userError "type argument absent")
  unless body.body.argumentCount == 1 && body.body.locals == #[argument,argument] && loaded.body == body.body do
    throw (IO.userError "identity source body did not instantiate exact argument type")
  let (again,repeated) ← must ((CallResolution.loadedBodyOfInstance prepared callee.instanceId).run retained)
  unless again.identity == loaded.identity && again.body == loaded.body && repeated.bodies == retained.bodies &&
      repeated.instances.constructed == retained.instances.constructed &&
      repeated.arena.constructedTypes == retained.arena.constructedTypes do
    throw (IO.userError "repeated source demand lost persistent body/compiler-world identity")
  let some relay := document.instances[2]? | throw (IO.userError "relay oracle absent")
  let relayStore ← must (InstanceArena.Store.ofSource initial.arena (document.instances.extract 0 2))
  let relayWorld := {initial with instances := relayStore}
  let (relayId,relayWorld) ← must ((CompilerInstance.item relay.instanceKind.defId relay.genericArgs).run relayWorld)
  let (relayBody,relayWorld) ← must ((CallResolution.loadedBodyOfInstance prepared relayId).run relayWorld)
  let (some relaySeed,relayWorld) ← must ((SourceMirCall.sourceIdentity relayBody.identity 0).run relayWorld)
    | throw (IO.userError "constructed body did not expose its own symbolic call")
  let ((relayCallee,_),_) ← must ((SourceMirCall.resolveInWorld document relaySeed).run relayWorld)
  unless relayCallee.arguments == expected.arguments do
    throw (IO.userError "constructed symbolic call lost body instance arguments")
  for invalid in [
      {document with mirTemplates := #[]},
      {document with mirTemplates := document.mirTemplates.map (fun source => {source with sourcePromoted := some 0})},
      {document with mirTemplates := document.mirTemplates ++ document.mirTemplates}] do
    let bad := {prepared with program := {program with input := invalid}}
    if ((CallResolution.loadedBodyOfInstance bad callee.instanceId).run world).isOk then
      throw (IO.userError "missing/promoted/duplicate source was accepted as an ordinary body")
  if ((program.resolveBodyIdentity (.ofCanonicalIndex 1000000)).run repeated).isOk then
    throw (IO.userError "unknown body identity was accepted")
  IO.println "PASS constructed LoadedBody identity, persistent body store and exact raw MIR demand; ABI remains separate"
