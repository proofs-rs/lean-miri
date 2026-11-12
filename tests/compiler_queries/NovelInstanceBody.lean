import Miri.Input.Decoder
import Miri.Input.SourceMirCall
import Miri.Input.CompilerInstance

/-! Runtime-store/body-demand component. Material instance prefix intentionally
omits both leaf instances. This is not executable-call or ABI evidence. -/
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
  let initial := {initial with instances := store}
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
  let (body,retained) ← must ((SourceMir.resolveInstanceBody document callee.instanceId).run world)
  unless body.instanceId == callee.instanceId && body.definitionId == some expected.kind.defId do
    throw (IO.userError "raw body demand lost complete instance ownership")
  let some (Miri.MIR.GenericArg.Type argument) := expected.arguments[0]? | throw (IO.userError "type argument absent")
  unless body.mir.argumentCount == 1 && body.mir.locals == #[argument,argument] do
    throw (IO.userError "identity source body did not instantiate exact argument type")
  let (again,repeated) ← must ((SourceMir.resolveInstanceBody document callee.instanceId).run retained)
  unless again.mir == body.mir && repeated.instances.constructed == retained.instances.constructed &&
      repeated.arena.constructedTypes == retained.arena.constructedTypes do
    throw (IO.userError "repeated source demand lost persistent compiler-world identity")
  for invalid in [
      {document with mirTemplates := #[]},
      {document with mirTemplates := document.mirTemplates.map (fun source => {source with sourcePromoted := some 0})},
      {document with mirTemplates := document.mirTemplates ++ document.mirTemplates}] do
    if ((SourceMir.resolveInstanceBody invalid callee.instanceId).run world).isOk then
      throw (IO.userError "missing/promoted/duplicate source was accepted as an ordinary body")
  IO.println "PASS novel instance Store and raw ordinary body demand retain one World; no LoadedBody/ABI claim"
