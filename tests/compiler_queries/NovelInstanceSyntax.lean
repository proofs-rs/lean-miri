import Miri.Input.Decoder
import Miri.Input.SourceMirCall
import MiriTests.Input.InstanceArenaSupport

/-! Focused fresh-rustc identity differential. The original complete callee row
is an oracle only, deliberately omitted from the three-row material prefix.
This establishes instance syntax construction, not body/ABI capability. -/
open Miri.Input
private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)
private def liftPure (result : Except String α) : InstanceArena.WorldM α :=
  match result with | .ok value => pure value | .error error => throw error

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected fresh source-call fixture")
  let document := (← must (decodeJson (← IO.FS.readFile path))).document
  let types ← must (TypeArena.World.ofDocument document)
  let some expected := document.instances[4]? | throw (IO.userError "rustc leaf<u64> oracle missing")
  let oracle ← must (InstanceArena.Key.ofSource types expected.instanceKind expected.genericArgs)
  let store ← must (InstanceArena.Store.ofSource types (document.instances.extract 0 3))
  let initial : InstanceArena.World := ⟨types,store⟩
  let some body := document.bodies.findIdx? (·.instanceId == 2)
    | throw (IO.userError "relay<u64> source body missing")
  let some source := document.bodies[body]? | throw (IO.userError "relay body missing")
  let .copyTemplate reference := source | throw (IO.userError "relay is not raw source MIR")
  let some template := document.mirTemplates[reference.templateId]?
    | throw (IO.userError "relay raw template missing")
  let some block := template.template.skeleton.blocks.findIdx? (fun block => match block.terminator.kind with
      | .call .. => true | _ => false) | throw (IO.userError "relay raw call missing")
  let some seed ← must (SourceMirCall.source document body block)
    | throw (IO.userError "relay call is not symbolic source")
  let action := SourceMirCall.resolveWith
    (fun arguments => do liftPure (GenericInstantiationWorld.ofArguments (← get).types 16384 arguments))
    (fun definition => do liftPure ((← get).types.definitionRef definition))
    (fun term => InstanceArena.World.typeAction (GenericInstantiationWorld.resolveType 16384 term))
    (fun definition arguments => InstanceArena.World.internInstance (.Item definition) arguments) seed
  let ((resolved,_),retained) ← must (action.run initial)
  unless resolved.instanceId == 3 do throw (IO.userError "novel instance ID is not dense after raw prefix")
  let .constructed actual ← must (retained.instances.lookup resolved.instanceId)
    | throw (IO.userError "callee was not constructed after omitted oracle row")
  unless actual == oracle do throw (IO.userError "raw source call differs from rustc full instance identity")
  let ((again,_),repeated) ← must (action.run retained)
  unless again.instanceId == resolved.instanceId && repeated.instances.constructed.size == 1 do
    throw (IO.userError "repeated source call lost persistent instance identity")
  if (initial.instances.lookup resolved.instanceId).isOk then
    throw (IO.userError "source call leaked instance state into independent execution")
  IO.println "PASS fresh rustc source call synthesizes exact omitted callee key; identity only, no body/ABI claim"
