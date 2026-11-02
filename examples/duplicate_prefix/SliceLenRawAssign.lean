import duplicate_prefix.SliceCarrier
import duplicate_prefix.RootPointerWrite
namespace DuplicatePrefix.SliceLenRawAssign
noncomputable section
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CanonicalConfigFacts PtrMetadataHelper PtrMetadataComplete PtrMetadataExecution SliceLenRawRvalue
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem compute_local2
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = SliceLenFacts.body.body)
    (identity : frame.bodyIdentity = SliceLenFacts.body.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.lenCall.callee) :
    CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler 2
      (Storage.withCurrent framesBefore frame machine) =
      .ok rawLayout (Storage.withCurrent framesBefore frame machine) := by
  have normalized := SliceLenFacts.normalized_local2 frame sourceBody identity callee
  unfold CompilerFrameContext.computeLocalLayout
  simp only [MachineHooks.currentFrame,Storage.withCurrent,Stack.currentFrame?,Array.back?_push,
    bind,EStateM.bind,get,getThe,MonadStateOf.get,EStateM.get,pure,EStateM.pure]
  rw [normalized]
  with_unfolding_all change (match PreparedReflection.actual.runtime.lookup 154 with
    | .ok value => EStateM.Result.ok value (Storage.withCurrent framesBefore frame machine)
    | .error error => EStateM.Result.error (StepError.unsupported s!"compiler frame query: {toString error}")
        (Storage.withCurrent framesBefore frame machine)) = _
  rw [raw_layout_eq]
  rfl

theorem destination2_uncached
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (valid : (2 : Miri.MIR.LocalId) < frame.locals.size)
    (uncached : (frame.locals[2]'(by omega)).layout = none)
    (body : frame.body = SliceLenFacts.body.body)
    (identity : frame.bodyIdentity = SliceLenFacts.body.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.lenCall.callee) :
    (ExecutionMachine.rvalueHooks
      (PreparedContracts.actualConfig options () remaining span) limits).evalPlace
      () ⟨2, #[]⟩ true (Storage.withCurrent framesBefore frame machine) =
    .ok (LocalPlaces.localRuntimePlace framesBefore.size
      (LocalPlaces.cachePlaceLayout frame 2 rawLayout valid) 2
      rawLayout)
      (Storage.withCurrent framesBefore
        (LocalPlaces.cachePlaceLayout frame 2 rawLayout valid) machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let state := Storage.withCurrent framesBefore frame machine
  let updatedFrame := LocalPlaces.cachePlaceLayout frame 2 rawLayout valid
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
  have resolve : hooks.resolveLayout () 2 state = .ok rawLayout state := by
    change config.projection.place.resolveLayout () 2 state = .ok rawLayout state
    rw [fields.projectionResolveLayout, fields.layout]
    exact compute_local2 framesBefore frame machine body identity callee
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
  have sized : rawLayout.layout.isSized = true := RootPointerCopy.raw_sized
  have localPlace := LocalPlaces.localToPlace_uncached hooks () framesBefore frame machine
    2 framesBefore.size rawLayout valid uncached sized
    resolve getFrame frameIndex setCached getCached indexCached
  have check := RootLocalStages.place_check_skipped options limits () remaining span debugOff
    ⟨2, #[]⟩ (LocalPlaces.localRuntimePlace framesBefore.size updatedFrame 2
      rawLayout) updated
  have evaluated := LocalPlaces.evalPlace_local_empty_uncached projection () 2 framesBefore
    frame machine framesBefore.size rawLayout valid
    (state := state) (updated := updated) localPlace check
  change PlaceDynamic.evalPlace projection () ⟨2, #[]⟩ true state = _
  exact evaluated

theorem write_carrier
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (old : Immediate Provenance)
    (carrier : Pointer Provenance ⊕ UInt64) (len : UInt64)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some rawLayout)
    (noClocks : frame.extra.dataRace = none) (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    let value := rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).writeImmediate () value
      (LocalPlaces.localRuntimePlace frames.size frame localId rawLayout) (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames (writeFrame frame localId value valid) machine) := by
  cases carrier with
  | inl pointer =>
    exact RootPointerWrite.write_raw_slice_shallow options limits remaining span debugOff fuel validationFuel
      frames frame machine localId old pointer len valid live cached noClocks ghost shallow
  | inr address =>
    exact RootPointerWrite.write_integer_slice_shallow options limits remaining span debugOff fuel validationFuel
      frames frame machine localId old address len valid live cached noClocks ghost shallow

theorem actual_raw_assignment
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (validationFuel : Nat)
    (validationEq : options.limits.validation = validationFuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (carrier : Pointer Provenance ⊕ UInt64) (len : UInt64)
    (carrierValid : SliceCarrier.Valid machine carrier len)
    (valid1 : (1 : Miri.MIR.LocalId) < frame.locals.size)
    (valid2 : (2 : Miri.MIR.LocalId) < frame.locals.size)
    (live1 : frame.locals[1].value = .live (.immediate
      (rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len)))
    (cached1 : frame.locals[1].layout = some SharedReferenceMetadata.sharedLayout)
    (live2 : frame.locals[2].value = .live (.immediate .uninit))
    (uncached2 : frame.locals[2].layout = none)
    (sourceBody : frame.body = SliceLenFacts.body.body)
    (identity : frame.bodyIdentity = SliceLenFacts.body.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.lenCall.callee)
    (noClocks : frame.extra.dataRace = none) (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (dynamicFuel : Nat) (dynamicEq : options.place.dynamicFuel = dynamicFuel+1)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let value := rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len
    evalRvalueIntoPlace
      (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (.RawPtr .Const ⟨1,#[.Deref]⟩) ⟨2,#[]⟩ (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames (copied2 frame valid2 value) machine) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let hooks := ExecutionMachine.rvalueHooks config limits
  let value := rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len
  let cachedFrame := cached2 frame valid2
  let state0 := Storage.withCurrent frames frame machine
  let state1 := Storage.withCurrent frames cachedFrame machine
  let dest := LocalPlaces.localRuntimePlace frames.size cachedFrame 2 rawLayout
  have sameTarget : config.access.runtime.base = (PreparedContracts.actualConfig options () remaining span).access.runtime.base := by
    rw [CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span,
      CanonicalConfigFacts.actual_access_runtime options () remaining span]
  have cachedValid1 : (1 : Miri.MIR.LocalId) < cachedFrame.locals.size := by
    simpa [cachedFrame,cached2,LocalPlaces.cachePlaceLayout] using valid1
  have cachedValid2 : (2 : Miri.MIR.LocalId) < cachedFrame.locals.size := by
    simpa [cachedFrame,cached2,LocalPlaces.cachePlaceLayout] using valid2
  have cachedLive1 : cachedFrame.locals[1].value = .live (.immediate (rawImmediate carrier config.access.runtime.base len)) := by
    rw [sameTarget]
    simpa [cachedFrame,cached2,LocalPlaces.cachePlaceLayout,Array.getElem_set] using live1
  have cachedLayout1 : cachedFrame.locals[1].layout = some SharedReferenceMetadata.sharedLayout := by
    simpa [cachedFrame,cached2,LocalPlaces.cachePlaceLayout,Array.getElem_set] using cached1
  have cachedLive2 : cachedFrame.locals[2].value = .live (.immediate .uninit) := by
    simpa [cachedFrame,cached2,LocalPlaces.cachePlaceLayout] using live2
  have cachedLayout2 : cachedFrame.locals[2].layout = some rawLayout := by
    simp [cachedFrame,cached2,LocalPlaces.cachePlaceLayout]
  have destination := destination2_uncached options limits (remaining+1) span debugOff frames frame machine
    valid2 uncached2 sourceBody identity callee
  have base := SliceLenRawPlace.actual_place_base_reference options limits (remaining+1) span frames cachedFrame machine sourceBody
  have dereference := SliceCarrier.actual_eval_deref options limits (remaining+1) span debugOff frames cachedFrame machine carrier len
    carrierValid cachedValid1 cachedLive1 cachedLayout1 noClocks ghost dynamicFuel dynamicEq cmp metadata notConstructed
  have staged := raw_staged_to_write options limits (remaining+1) span carrier len false ⟨1,#[.Deref]⟩ ⟨2,#[]⟩ dest
    state0 state1 rfl destination base dereference
  rw [staged]
  rw [sameTarget]
  exact write_carrier options limits remaining span debugOff validationFuel validationEq frames cachedFrame machine
    2 .uninit carrier len cachedValid2 cachedLive2 cachedLayout2 noClocks ghost shallow

#print axioms actual_raw_assignment

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``actual_raw_assignment) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved raw assignment dependency {dependency}"

end
end DuplicatePrefix.SliceLenRawAssign
