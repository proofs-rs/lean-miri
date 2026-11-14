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
  match (CallResolution.loadedBodyOfInstance prepared callee.instanceId).run world with
  | .error "constructed instance has no exact rustc body result" => pure ()
  | .error error => throw (IO.userError s!"unexpected constructed body error: {error}")
  | .ok _ => throw (IO.userError "constructed instance borrowed a rustc body result")
  IO.println "PASS constructed instance body requires exact rustc result"
