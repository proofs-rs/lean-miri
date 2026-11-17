import duplicate_prefix.RootGenericBoolWrite
import duplicate_prefix.RootFatRawPointerValidity
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.RootPointerWrite
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
private theorem write_validated
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (old : Immediate Provenance) (layout : LocalLayout) (value : Immediate Provenance)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some layout)
    (noClocks : frame.extra.dataRace = none)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (sized : layout.layout.isSized = true)
    (validation : ∀ (postFrame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
      (postValid : localId < postFrame.locals.size),
      postFrame.locals[localId].value = .live (.immediate value) →
      postFrame.locals[localId].layout = some layout →
      ValidityMachine.validateRuntime (PreparedContracts.actualConfig options () remaining span).validity
        () (fuel + 1) (LocalPlaces.localRuntimePlace framesBefore.size postFrame localId layout) true
        (Storage.withCurrent framesBefore postFrame machine) = .ok () (Storage.withCurrent framesBefore postFrame machine)) :
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).writeImmediate
      () value
      (LocalPlaces.localRuntimePlace framesBefore.size frame localId layout)
      (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore {frame with locals := (frame.locals.set localId
        {value := .live (.immediate value), layout := frame.locals[localId].layout} valid)} machine) := by
  let config := PreparedContracts.actualConfig options () (remaining + 1) span
  let hooks := (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits)).place
  let postFrame := {frame with locals := (frame.locals.set localId
    {value := .live (.immediate value), layout := frame.locals[localId].layout} valid)}
  let postState := Storage.withCurrent framesBefore postFrame machine
  have fields := CanonicalConfigFacts.actual_fields options () (remaining + 1) span
  have physical := RootUsizeWrite.write_local_no_validate options limits (remaining + 1) span debugOff framesBefore frame machine localId
    old value layout valid live sized noClocks ghostFalse
  have enforced : hooks.enforceValidity () layout postState = .ok true postState := by
    change config.projection.place.enforceValidity () layout postState = _
    rw [fields.projectionEnforce]
    simp [ValidityMachine.enforceValidity, postState, Storage.withCurrent, shallow,
      get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure]
  have postValid : localId < postFrame.locals.size := by simpa only [postFrame, Array.size_set] using valid
  have postLive : postFrame.locals[localId].value = .live (.immediate value) := by
    simp [postFrame, valid]
  have postCached : postFrame.locals[localId].layout = some layout := by
    simpa only [postFrame, Array.getElem_set_self] using cached
  have validated : hooks.validate ()
      (LocalPlaces.localRuntimePlace framesBefore.size frame localId layout) postState = .ok () postState := by
    change config.projection.place.validate () _ postState = _
    rw [fields.projectionValidate, CanonicalConfigFacts.actual_validate_successor, validationFuel]
    change ValidityMachine.validateRuntime (PreparedContracts.actualConfig options () remaining span).validity ()
      (fuel + 1) (LocalPlaces.localRuntimePlace framesBefore.size postFrame localId layout) true postState = _
    exact validation postFrame postValid postLive postCached
  change writePlaceImmediate hooks () value
    (LocalPlaces.localRuntimePlace framesBefore.size frame localId layout) _ = _
  unfold writePlaceImmediate
  simp only [bind, EStateM.bind]
  rw [physical]
  simp only [bind, EStateM.bind]
  erw [enforced]
  exact validated

theorem write_mut_pointer_shallow
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (old : Immediate Provenance) (value : Scalar Provenance)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some CopyCompilerFacts.destPointerLayout)
    (noClocks : frame.extra.dataRace = none)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).writeImmediate
      () (.scalar value)
      (LocalPlaces.localRuntimePlace framesBefore.size frame localId CopyCompilerFacts.destPointerLayout)
      (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore {frame with locals := (frame.locals.set localId
        {value := .live (.immediate (.scalar value)), layout := frame.locals[localId].layout} valid)} machine) := by
  apply write_validated options limits remaining span debugOff fuel validationFuel framesBefore frame machine
    localId old CopyCompilerFacts.destPointerLayout (.scalar value) valid live cached noClocks ghostFalse shallow RootRawPointerValidity.mut_pointer_sized
  intro postFrame postValid postLive postCached
  exact RootRawPointerValidity.validate_nested_mut_pointer_shallow options remaining span debugOff fuel framesBefore postFrame machine localId value
    postValid postLive postCached ghostFalse shallow

theorem write_const_pointer_shallow
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (old : Immediate Provenance) (value : Scalar Provenance)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some CopyCompilerFacts.sourcePointerLayout)
    (noClocks : frame.extra.dataRace = none)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).writeImmediate
      () (.scalar value)
      (LocalPlaces.localRuntimePlace framesBefore.size frame localId CopyCompilerFacts.sourcePointerLayout)
      (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore {frame with locals := (frame.locals.set localId
        {value := .live (.immediate (.scalar value)), layout := frame.locals[localId].layout} valid)} machine) := by
  apply write_validated options limits remaining span debugOff fuel validationFuel framesBefore frame machine
    localId old CopyCompilerFacts.sourcePointerLayout (.scalar value) valid live cached noClocks ghostFalse shallow RootRawPointerValidity.const_pointer_sized
  intro postFrame postValid postLive postCached
  exact RootRawPointerValidity.validate_nested_const_pointer_shallow options remaining span debugOff fuel framesBefore postFrame machine localId value
    postValid postLive postCached ghostFalse shallow

theorem write_raw_slice_shallow
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (old : Immediate Provenance) (pointer : Pointer Provenance) (len : UInt64)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some PtrMetadataHelper.rawLayout)
    (noClocks : frame.extra.dataRace = none)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).writeImmediate
      () ((RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base pointer len PtrMetadataHelper.rawLayout).imm)
      (LocalPlaces.localRuntimePlace framesBefore.size frame localId PtrMetadataHelper.rawLayout)
      (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore {frame with locals := (frame.locals.set localId
        {value := .live (.immediate ((RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base pointer len PtrMetadataHelper.rawLayout).imm)), layout := frame.locals[localId].layout} valid)} machine) := by
  apply write_validated options limits remaining span debugOff fuel validationFuel framesBefore frame machine
    localId old PtrMetadataHelper.rawLayout ((RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base pointer len PtrMetadataHelper.rawLayout).imm) valid live cached noClocks ghostFalse shallow (by with_unfolding_all rfl)
  intro postFrame postValid postLive postCached
  exact RootFatRawPointerValidity.validate_nested_raw_slice_shallow options remaining span debugOff fuel framesBefore postFrame machine localId pointer len
    postValid postLive postCached ghostFalse shallow

theorem write_integer_slice_shallow
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (old : Immediate Provenance) (address len : UInt64)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some PtrMetadataHelper.rawLayout)
    (noClocks : frame.extra.dataRace = none)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).writeImmediate
      () ((RetagReferencePlace.integerSliceValue address len PtrMetadataHelper.rawLayout).imm)
      (LocalPlaces.localRuntimePlace framesBefore.size frame localId PtrMetadataHelper.rawLayout)
      (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore {frame with locals := (frame.locals.set localId
        {value := .live (.immediate ((RetagReferencePlace.integerSliceValue address len PtrMetadataHelper.rawLayout).imm)), layout := frame.locals[localId].layout} valid)} machine) := by
  apply write_validated options limits remaining span debugOff fuel validationFuel framesBefore frame machine
    localId old PtrMetadataHelper.rawLayout ((RetagReferencePlace.integerSliceValue address len PtrMetadataHelper.rawLayout).imm) valid live cached noClocks ghostFalse shallow (by with_unfolding_all rfl)
  intro postFrame postValid postLive postCached
  exact RootFatRawPointerValidity.validate_nested_integer_slice_shallow options remaining span debugOff fuel framesBefore postFrame machine localId address len
    postValid postLive postCached ghostFalse shallow

theorem write_validated_local
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (old : Immediate Provenance) (layout : LocalLayout) (value : Immediate Provenance)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some layout)
    (noClocks : frame.extra.dataRace = none)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (sized : layout.layout.isSized = true)
    (validation : ∀ (postFrame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
      (postValid : localId < postFrame.locals.size),
      postFrame.locals[localId].value = .live (.immediate value) →
      postFrame.locals[localId].layout = some layout →
      ValidityMachine.validateRuntime (PreparedContracts.actualConfig options () remaining span).validity
        () (fuel + 1) (LocalPlaces.localRuntimePlace framesBefore.size postFrame localId layout) true
        (Storage.withCurrent framesBefore postFrame machine) = .ok () (Storage.withCurrent framesBefore postFrame machine)) :
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).writeImmediate
      () value
      (LocalPlaces.localRuntimePlace framesBefore.size frame localId layout)
      (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore {frame with locals := (frame.locals.set localId
        {value := .live (.immediate value), layout := frame.locals[localId].layout} valid)} machine) := by
  exact write_validated options limits remaining span debugOff fuel validationFuel framesBefore frame machine
    localId old layout value valid live cached noClocks ghostFalse shallow sized validation

open Lean Elab Command in
run_cmd do
  for declaration in [``write_validated_local, ``write_validated, ``write_mut_pointer_shallow, ``write_const_pointer_shallow,
      ``write_raw_slice_shallow, ``write_integer_slice_shallow] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
end DuplicatePrefix.RootPointerWrite
