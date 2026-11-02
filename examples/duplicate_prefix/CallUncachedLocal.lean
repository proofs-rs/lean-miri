import duplicate_prefix.RootOperandCopy
import duplicate_prefix.RootLocalStages

namespace DuplicatePrefix.CallUncachedLocal
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem runtime_uncached
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (layout : LocalLayout)
    (valid : localId < frame.locals.size)
    (uncached : (frame.locals[localId]'(by omega)).layout = none)
    (sized : layout.layout.isSized = true)
    (query : CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler localId
      (Storage.withCurrent framesBefore frame machine) = .ok layout (Storage.withCurrent framesBefore frame machine)) :
    (ExecutionMachine.rvalueHooks
      (PreparedContracts.actualConfig options () remaining span) limits).evalPlace
      () ⟨localId, #[]⟩ false (Storage.withCurrent framesBefore frame machine) =
    .ok (LocalPlaces.localRuntimePlace framesBefore.size
      (LocalPlaces.cachePlaceLayout frame localId layout valid) localId
      layout)
      (Storage.withCurrent framesBefore
        (LocalPlaces.cachePlaceLayout frame localId layout valid) machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let state := Storage.withCurrent framesBefore frame machine
  let updatedFrame := LocalPlaces.cachePlaceLayout frame localId layout valid
  let updated := Storage.withCurrent framesBefore updatedFrame machine
  let projection := ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits)
  let hooks := projection.place
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  have getFrame : hooks.getFrame state = .ok frame state := by
    change config.projection.place.getFrame state = .ok frame state
    rw [fields.projectionGetFrame]
    exact Storage.current_frame framesBefore frame machine
  have frameIndex : hooks.frameIndex state = .ok framesBefore.size state := by
    change config.projection.place.frameIndex state = .ok framesBefore.size state
    rw [fields.projectionFrameIndex]
    simp [state, Storage.withCurrent, Stack.frameIndex, Array.isEmpty_push,
      bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
      pure, EStateM.pure, Except.pure, Except.bind]
  have resolve : hooks.resolveLayout () localId state = .ok layout state := by
    change config.projection.place.resolveLayout () localId state = .ok layout state
    rw [fields.projectionResolveLayout, fields.layout]
    exact query
  have setCached : hooks.setFrame updatedFrame state = .ok () updated := by
    change config.projection.place.setFrame updatedFrame state = .ok () updated
    rw [fields.projectionSetFrame]
    exact Storage.set_current_frame framesBefore frame updatedFrame machine
  have getCached : hooks.getFrame updated = .ok updatedFrame updated := by
    change config.projection.place.getFrame updated = .ok updatedFrame updated
    rw [fields.projectionGetFrame]
    exact Storage.current_frame framesBefore updatedFrame machine
  have indexCached : hooks.frameIndex updated = .ok framesBefore.size updated := by
    change config.projection.place.frameIndex updated = .ok framesBefore.size updated
    rw [fields.projectionFrameIndex]
    simp [updated, Storage.withCurrent, Stack.frameIndex, Array.isEmpty_push,
      bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
      pure, EStateM.pure, Except.pure, Except.bind]
  have localPlace := LocalPlaces.localToPlace_uncached hooks () framesBefore frame machine
    localId framesBefore.size layout valid uncached sized
    resolve getFrame frameIndex setCached getCached indexCached
  have check := RootLocalStages.place_check_skipped options limits () remaining span debugOff
    ⟨localId, #[]⟩ (LocalPlaces.localRuntimePlace framesBefore.size updatedFrame localId
      layout) updated
  have evaluated := LocalPlaces.evalPlace_local_empty_uncached projection () localId framesBefore
    frame machine framesBefore.size layout valid
    (state := state) (updated := updated) localPlace check
  change PlaceDynamic.evalPlace projection () ⟨localId, #[]⟩ false state = _
  exact evaluated

theorem uncached
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (id : MIR.LocalId) (layout : LocalLayout)
    (valid : id < frame.locals.size) (notCached : frame.locals[id].layout = none)
    (sized : layout.layout.isSized = true)
    (query : CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler id
      (Storage.withCurrent frames frame machine) = .ok layout (Storage.withCurrent frames frame machine)) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).evalPlace ()
      ⟨id,#[]⟩ false (Storage.withCurrent frames frame machine) =
      .ok (LocalPlaces.localRuntimePlace frames.size (LocalPlaces.cachePlaceLayout frame id layout valid) id layout).stackView
        (Storage.withCurrent frames (LocalPlaces.cachePlaceLayout frame id layout valid) machine) := by
  let cfg := PreparedContracts.actualConfig options () remaining span
  let projection := ExecutionMachine.projectionHooks (ExecutionMachine.withValidation cfg limits)
  have evaluated := runtime_uncached options limits remaining span debug frames frame machine id layout valid notCached sized query
  change PlaceDynamic.evalPlace projection () ⟨id,#[]⟩ false _ = _ at evaluated
  change ((fun value => pure value.stackView) =<< PlaceDynamic.evalPlace projection () ⟨id,#[]⟩ false) _ = _
  simp only [Bind.bindLeft,Bind.bind,EStateM.bind,evaluated,pure,Pure.pure,EStateM.pure]
end DuplicatePrefix.CallUncachedLocal
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.CallUncachedLocal.uncached) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved uncached call destination dependency {dependency}"
