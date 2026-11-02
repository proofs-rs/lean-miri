import duplicate_prefix.AsMutPtrCarrier
import duplicate_prefix.AsMutPtrRawRvalue
import duplicate_prefix.AsMutPtrWrites
namespace DuplicatePrefix.AsMutPtrRawAssign
noncomputable section
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CanonicalConfigFacts PtrMetadataComplete PtrMetadataExecution SliceLenRawRvalue AsMutPtrRawRvalue AsMutPtrFacts
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
def cached4 (frame : CompilerFrameContext.ActualFrame) (valid : (4 : Miri.MIR.LocalId) < frame.locals.size) :=
  LocalPlaces.cachePlaceLayout frame 4 rawLayout valid

def copied4 (frame : CompilerFrameContext.ActualFrame) (valid : (4 : Miri.MIR.LocalId) < frame.locals.size)
    (value : Immediate Provenance) :=
  writeFrame (cached4 frame valid) 4 value (by simpa [cached4,LocalPlaces.cachePlaceLayout] using valid)

theorem normalized_local4 (frame : CompilerFrameContext.ActualFrame)
    (sourceBody : frame.body = HelperCompilerFacts.asMutPtrBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.asMutPtrBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.asMutPtrCall.callee) :
    CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler frame 4 = .ok 204 := by
  unfold CompilerFrameContext.normalizedLocalType CompilerFrameContext.normalizedBody CompilerFrameContext.bodyOfFrame
  rw [sourceBody,identity,callee]
  with_unfolding_all rfl

theorem actual_reference_not_raw
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) :
    (PreparedContracts.actualConfig options () remaining span).isRawPointer () 3 = pure false := by
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).isRawPointer]
  funext state
  dsimp only
  with_unfolding_all rfl

theorem actual_place_base_reference
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = HelperCompilerFacts.asMutPtrBody.body) :
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () remaining span) limits).placeBaseRaw ()
      ⟨1,#[.Deref]⟩ (Storage.withCurrent frames frame machine) =
      .ok false (Storage.withCurrent frames frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  change (do
    let frame ← MachineHooks.currentFrame
    let some ty := frame.body.locals[1]? | throw (StepError.invalidProgram "raw place base local missing")
    config.isRawPointer () ty) (Storage.withCurrent frames frame machine) = _
  simp only [MachineHooks.currentFrame,Storage.withCurrent,Stack.currentFrame?,Array.back?_push,
    bind,Bind.bind,EStateM.bind,get,getThe,MonadStateOf.get,EStateM.get,pure,Pure.pure,EStateM.pure]
  rw [sourceBody]
  with_unfolding_all change config.isRawPointer () 3 (Storage.withCurrent frames frame machine) = _
  exact congrFun (actual_reference_not_raw options remaining span) (Storage.withCurrent frames frame machine)

theorem compute_local4
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = HelperCompilerFacts.asMutPtrBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.asMutPtrBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.asMutPtrCall.callee) :
    CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler 4
      (Storage.withCurrent framesBefore frame machine) =
      .ok rawLayout (Storage.withCurrent framesBefore frame machine) := by
  have normalized := normalized_local4 frame sourceBody identity callee
  unfold CompilerFrameContext.computeLocalLayout
  simp only [MachineHooks.currentFrame,Storage.withCurrent,Stack.currentFrame?,Array.back?_push,
    bind,EStateM.bind,get,getThe,MonadStateOf.get,EStateM.get,pure,EStateM.pure]
  rw [normalized]
  with_unfolding_all change (match PreparedReflection.actual.runtime.lookup 204 with
    | .ok value => EStateM.Result.ok value (Storage.withCurrent framesBefore frame machine)
    | .error error => EStateM.Result.error (StepError.unsupported s!"compiler frame query: {toString error}")
        (Storage.withCurrent framesBefore frame machine)) = _
  rw [AsMutPtrFacts.raw_layout_eq]
  rfl

theorem destination4_uncached
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (valid : (4 : Miri.MIR.LocalId) < frame.locals.size)
    (uncached : (frame.locals[4]'(by omega)).layout = none)
    (body : frame.body = HelperCompilerFacts.asMutPtrBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.asMutPtrBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.asMutPtrCall.callee) :
    (ExecutionMachine.rvalueHooks
      (PreparedContracts.actualConfig options () remaining span) limits).evalPlace
      () ⟨4, #[]⟩ true (Storage.withCurrent framesBefore frame machine) =
    .ok (LocalPlaces.localRuntimePlace framesBefore.size
      (LocalPlaces.cachePlaceLayout frame 4 rawLayout valid) 4
      rawLayout)
      (Storage.withCurrent framesBefore
        (LocalPlaces.cachePlaceLayout frame 4 rawLayout valid) machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let state := Storage.withCurrent framesBefore frame machine
  let updatedFrame := LocalPlaces.cachePlaceLayout frame 4 rawLayout valid
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
  have resolve : hooks.resolveLayout () 4 state = .ok rawLayout state := by
    change config.projection.place.resolveLayout () 4 state = .ok rawLayout state
    rw [fields.projectionResolveLayout, fields.layout]
    exact compute_local4 framesBefore frame machine body identity callee
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
  have sized : rawLayout.layout.isSized = true := AsMutPtrFacts.raw_sized
  have localPlace := LocalPlaces.localToPlace_uncached hooks () framesBefore frame machine
    4 framesBefore.size rawLayout valid uncached sized
    resolve getFrame frameIndex setCached getCached indexCached
  have check := RootLocalStages.place_check_skipped options limits () remaining span debugOff
    ⟨4, #[]⟩ (LocalPlaces.localRuntimePlace framesBefore.size updatedFrame 4
      rawLayout) updated
  have evaluated := LocalPlaces.evalPlace_local_empty_uncached projection () 4 framesBefore
    frame machine framesBefore.size rawLayout valid
    (state := state) (updated := updated) localPlace check
  change PlaceDynamic.evalPlace projection () ⟨4, #[]⟩ true state = _
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
    exact AsMutPtrWrites.write_mut_slice_shallow options limits remaining span debugOff fuel validationFuel
      frames frame machine localId old pointer len valid live cached noClocks ghost shallow
  | inr address =>
    exact AsMutPtrWrites.write_integer_mut_slice_shallow options limits remaining span debugOff fuel validationFuel
      frames frame machine localId old address len valid live cached noClocks ghost shallow

theorem actual_raw_assignment
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (validationFuel : Nat)
    (validationEq : options.limits.validation = validationFuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (carrier : Pointer Provenance ⊕ UInt64) (len : UInt64)
    (carrierValid : AsMutPtrCarrier.Valid machine carrier len)
    (valid1 : (1 : Miri.MIR.LocalId) < frame.locals.size)
    (valid4 : (4 : Miri.MIR.LocalId) < frame.locals.size)
    (live1 : frame.locals[1].value = .live (.immediate
      (rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len)))
    (cached1 : frame.locals[1].layout = some ActualReferenceMetadata.reference)
    (live4 : frame.locals[4].value = .live (.immediate .uninit))
    (uncached4 : frame.locals[4].layout = none)
    (sourceBody : frame.body = HelperCompilerFacts.asMutPtrBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.asMutPtrBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.asMutPtrCall.callee)
    (noClocks : frame.extra.dataRace = none) (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (dynamicFuel : Nat) (dynamicEq : options.place.dynamicFuel = dynamicFuel+1)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let value := rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len
    evalRvalueIntoPlace
      (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (.RawPtr .Mut ⟨1,#[.Deref]⟩) ⟨4,#[]⟩ (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames (copied4 frame valid4 value) machine) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let hooks := ExecutionMachine.rvalueHooks config limits
  let value := rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len
  let cachedFrame := cached4 frame valid4
  let state0 := Storage.withCurrent frames frame machine
  let state1 := Storage.withCurrent frames cachedFrame machine
  let dest := LocalPlaces.localRuntimePlace frames.size cachedFrame 4 rawLayout
  have sameTarget : config.access.runtime.base = (PreparedContracts.actualConfig options () remaining span).access.runtime.base := by
    rw [CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span,
      CanonicalConfigFacts.actual_access_runtime options () remaining span]
  have cachedValid1 : (1 : Miri.MIR.LocalId) < cachedFrame.locals.size := by
    simpa [cachedFrame,cached4,LocalPlaces.cachePlaceLayout] using valid1
  have cachedValid4 : (4 : Miri.MIR.LocalId) < cachedFrame.locals.size := by
    simpa [cachedFrame,cached4,LocalPlaces.cachePlaceLayout] using valid4
  have cachedLive1 : cachedFrame.locals[1].value = .live (.immediate (rawImmediate carrier config.access.runtime.base len)) := by
    rw [sameTarget]
    simpa [cachedFrame,cached4,LocalPlaces.cachePlaceLayout,Array.getElem_set] using live1
  have cachedLayout1 : cachedFrame.locals[1].layout = some ActualReferenceMetadata.reference := by
    simpa [cachedFrame,cached4,LocalPlaces.cachePlaceLayout,Array.getElem_set] using cached1
  have cachedLive4 : cachedFrame.locals[4].value = .live (.immediate .uninit) := by
    simpa [cachedFrame,cached4,LocalPlaces.cachePlaceLayout] using live4
  have cachedLayout4 : cachedFrame.locals[4].layout = some rawLayout := by
    simp [cachedFrame,cached4,LocalPlaces.cachePlaceLayout]
  have destination := destination4_uncached options limits (remaining+1) span debugOff frames frame machine
    valid4 uncached4 sourceBody identity callee
  have base := actual_place_base_reference options limits (remaining+1) span frames cachedFrame machine sourceBody
  have dereference := AsMutPtrCarrier.actual_eval_deref options limits (remaining+1) span debugOff frames cachedFrame machine carrier len
    carrierValid cachedValid1 cachedLive1 cachedLayout1 noClocks ghost dynamicFuel dynamicEq cmp metadata notConstructed
  have staged := raw_staged_to_write options limits (remaining+1) span carrier len false ⟨1,#[.Deref]⟩ ⟨4,#[]⟩ dest
    state0 state1 rfl destination base dereference
  rw [staged]
  rw [sameTarget]
  exact write_carrier options limits remaining span debugOff validationFuel validationEq frames cachedFrame machine
    4 .uninit carrier len cachedValid4 cachedLive4 cachedLayout4 noClocks ghost shallow

#print axioms actual_raw_assignment

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``actual_raw_assignment) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved raw assignment dependency {dependency}"

end
end DuplicatePrefix.AsMutPtrRawAssign
