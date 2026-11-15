import Miri.Frontend.FoundationEntrySeed
import Miri.Input.SourceCompilerBodies
import Miri.Input.CompilerFrameContext
import Miri.Input.CompilerFrameMetadata
import Miri.Input.CompilerAllocationBacktrace
import Miri.Input.CompilerPlaceTypes
open Lean Miri Miri.Input Miri.Interpreter Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def rejects (value : Except String α) : IO Unit :=
  match value with | .error _ => pure () | .ok _ => throw (IO.userError "invalid frame identity accepted")

def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected genuine custom source")
  let document ← checked (decode (← checked (Json.parse (← IO.FS.readFile path))))
  let initial ← checked (compilerEntrySeed document)
  let some node := initial.canonical.instances.find? (·.defPath == some "main")
    | throw (IO.userError "main identity absent")
  let (world,loaded) ← checked (SourceCompilerBodies.demandLoadedBody initial node.id)
  let some returnType := loaded.body.locals[0]? | throw (IO.userError "return local absent")
  let runtime ← checked (RuntimeMetadata.ofDocument world.canonical |>.mapError toString)
  let layout ← checked (runtime.lookup returnType |>.mapError toString)
  let identity := (LocalsIdentitySupply.allocate ⟨0⟩).2
  let destination := RuntimeStackPlace.frameLocal 0 0 none layout identity
  let extra : MachineHooks.FrameExtra := ⟨none,none,0,none⟩
  let frame := Frame.create loaded node.id extra (.stop true) destination
    ⟨world.canonical.queries.session.rootSpan⟩ identity
  let actual ← checked (CompilerFrameContext.worldBodyOfFrame world frame)
  unless actual.mir == loaded.body do throw (IO.userError "current body content changed")
  unless (← checked (CompilerFrameContext.localType world frame 0)) == returnType do
    throw (IO.userError "current local type changed")
  let key ← checked (SourceCompilerWorld.keyOf world node.id)
  unless (← checked (SourceCompilerFrame.definitionCrate world node.id)) == key.definition.crateIndex do
    throw (IO.userError "current definition crate identity changed")
  let some source := world.canonical.sourceMaterial | throw (IO.userError "typed source absent")
  let some abi := source.abi | throw (IO.userError "source function headers absent")
  let some header := abi.functions.find? (·.definition == key.definition)
    | throw (IO.userError "main source header absent")
  unless (← checked (CompilerFrameMetadata.requiresCallerLocation world node.id)) == header.attributes.trackCaller do
    throw (IO.userError "source caller-location attribute changed")
  rejects (CompilerFrameMetadata.requiresCallerLocation
    {world with canonical := {world.canonical with sourceMaterial := some {source with abi := none}}} node.id)
  let scope ← checked (CompilerFrameMetadata.sourceScope world loaded.identity node.id loaded.body 0)
  let some actualScope := actual.sourceScopes[0]? | throw (IO.userError "source scope absent")
  unless scope.inlinedParentScope == actualScope.inlinedParent do
    throw (IO.userError "current scope metadata changed")
  let backtrace ← checked (CompilerAllocationBacktrace.collect world #[frame])
  unless backtrace.size == 1 && backtrace[0]?.map Prod.fst == some node.id do
    throw (IO.userError "current physical backtrace identity changed")
  let place := MIR.Place.mk 0 #[]
  let expected ← checked (CompilerPlaceTypes.expectedLayout runtime world frame place)
  unless expected == layout do throw (IO.userError "whole-local place type changed")
  rejects (CompilerFrameMetadata.sourceScope initial loaded.identity node.id loaded.body 0)
  rejects (CompilerAllocationBacktrace.collect initial #[frame])
  rejects (CompilerPlaceTypes.expectedLayout runtime initial frame place)
  rejects (CompilerFrameMetadata.sourceScope world loaded.identity node.id loaded.body actual.sourceScopes.size)
  rejects (CompilerFrameContext.worldBodyOfFrame initial frame)
  rejects (CompilerFrameContext.worldBodyOfFrame world
    {frame with bodyIdentity := .ofCanonicalIndex world.canonical.bodies.size})
  rejects (CompilerFrameContext.worldBodyOfFrame world
    {frame with functionInstance := world.canonical.instances.size})
  rejects (CompilerFrameContext.worldBodyOfFrame world
    {frame with body := {frame.body with argumentCount := frame.body.argumentCount+1}})
  IO.println "live frame context: actual demanded body/local type; stale World/wrong identity/instance/MIR reject"
