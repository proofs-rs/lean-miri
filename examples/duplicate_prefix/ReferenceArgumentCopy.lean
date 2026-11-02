import duplicate_prefix.ActualEmptyReference
import duplicate_prefix.RootUsizeWrite
import duplicate_prefix.PrimitiveArgumentCopy

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace DuplicatePrefix.ReferenceArgumentCopy
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open ActualReferenceMetadata

theorem reference_no_padding : CompilerCopy.hasPadding PreparedReflection.actual.compiler.runtime false reference = .ok false := by
  with_unfolding_all rfl

/-- Internal composition at the source nested-validation callback. The public
empty/positive wrappers discharge this callback from actual metadata and state. -/
theorem copy_with_nested_validation
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : MIR.LocalId) (old value : Immediate Provenance)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some reference)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (view : RuntimeStackPlace Provenance)
    (destination : view.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size frame localId reference)
    (after : CanonicalConfigFacts.RootState)
    (validated : ValidityMachine.validateRuntime
      (PreparedContracts.actualConfig options () remaining span).validity () options.limits.validation
      (LocalPlaces.localRuntimePlace frames.size frame localId reference) true
      (Storage.withCurrent frames {frame with locals := (frame.locals.set localId
        {value := .live (.immediate value), layout := frame.locals[localId].layout} valid)} machine) =
      .ok () after) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).copyAllowTransmute ()
      ⟨.immediate value, reference⟩ view (Storage.withCurrent frames frame machine) = .ok () after := by
  let cfg := PreparedContracts.actualConfig options () (remaining + 1) span
  let bound := ExecutionMachine.withValidation cfg limits
  let place := (ExecutionMachine.projectionHooks bound).place
  let dest := LocalPlaces.localRuntimePlace frames.size frame localId reference
  let postFrame := {frame with locals := (frame.locals.set localId
    {value := .live (.immediate value), layout := frame.locals[localId].layout} valid)}
  let postState := Storage.withCurrent frames postFrame machine
  have fields := CanonicalConfigFacts.actual_fields options () (remaining + 1) span
  have compatible : bound.copy.compatible = CompilerCovariance.compatible PreparedReflection.actual.compiler false := by
    change cfg.copy.compatible = _
    rw [fields.copyCompatible, debugOff]
  have flag := GenericCallReturn.same_layout_transmute_flag place bound.copy PreparedReflection.actual.compiler ()
    reference value dest rfl compatible
  have exactCopy : copyRuntimePlace place bound.copy () ⟨.immediate value, reference⟩ dest true =
      (ExecutionMachine.rvalueHooks cfg limits).copyOp () ⟨.immediate value, reference⟩ dest := by
    rw [flag]; rfl
  have copy := ActualScalarCopy.actual_copy_no_padding options limits (remaining + 1) span debugOff
    reference value dest rfl reference_no_padding reference_sized
  have physical := RootUsizeWrite.write_local_no_validate options limits (remaining + 1) span debugOff
    frames frame machine localId old value reference valid live reference_sized noClocks ghost
  have enforced : place.enforceValidity () reference postState = .ok true postState := by
    change cfg.projection.place.enforceValidity () reference postState = _
    rw [fields.projectionEnforce]
    simp [ValidityMachine.enforceValidity, postState, Storage.withCurrent, shallow,
      get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure]
  have validation : place.validate () dest postState = .ok () after := by
    change cfg.projection.place.validate () dest postState = _
    rw [fields.projectionValidate, CanonicalConfigFacts.actual_validate_successor]
    exact validated
  change copyRuntimePlace place bound.copy () ⟨.immediate value, reference⟩ view.toRuntimePlace true _ = _
  rw [destination, exactCopy, copy]
  change writePlaceImmediate place () value dest _ = _
  unfold writePlaceImmediate
  simp only [bind, EStateM.bind]
  rw [physical]
  simp only [bind, EStateM.bind]
  erw [enforced]
  exact validation


theorem copy_empty_argument
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (precise : options.retag.preciseInteriorMut = false)
    (implicitWrites : options.retag.implicitWrites = false)
    (debugOff : options.place.debugAssertions = false)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel + 1)
    (validationEq : options.limits.validation = validityFuel + 1)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : MIR.LocalId) (old : Immediate Provenance) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some reference)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (address : UInt64) (nonzero : address ≠ 0)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false)
    (view : RuntimeStackPlace Provenance)
    (destination : view.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size frame localId reference) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).copyAllowTransmute ()
      ⟨.immediate (RetagReferencePlace.integerSliceValue address 0 reference).imm, reference⟩ view
      (Storage.withCurrent frames frame machine) = .ok ()
      (TypedRetagEmpty.afterTag (Storage.withCurrent frames {frame with locals := (frame.locals.set localId
        {value := .live (.immediate (RetagReferencePlace.integerSliceValue address 0 reference).imm),
         layout := frame.locals[localId].layout} valid)} machine) tracker fresh) := by
  let value := (RetagReferencePlace.integerSliceValue address 0 reference).imm
  let postFrame := {frame with locals := (frame.locals.set localId
    {value := .live (.immediate value), layout := frame.locals[localId].layout} valid)}
  have postValid : localId < postFrame.locals.size := by simpa only [postFrame, Array.size_set] using valid
  have postLive : postFrame.locals[localId].value = .live (.immediate value) := by simp [postFrame, valid]
  have postCached : postFrame.locals[localId].layout = some reference := by
    simpa only [postFrame, Array.getElem_set_self] using cached
  apply copy_with_nested_validation options limits remaining span debugOff frames frame machine localId old value
    valid live cached noClocks ghost shallow view destination
  rw [validationEq]
  exact ActualEmptyReference.validate options remaining span cmp precise implicitWrites debugOff dynamicFuel validityFuel fuelEq
    frames postFrame machine localId postValid address nonzero postLive postCached ghost shallow tracker enabled mode fresh metadata notConstructed

end DuplicatePrefix.ReferenceArgumentCopy
open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.ReferenceArgumentCopy.reference_no_padding,
      ``DuplicatePrefix.ReferenceArgumentCopy.copy_with_nested_validation,
      ``DuplicatePrefix.ReferenceArgumentCopy.copy_empty_argument] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved reference argument composition dependency {dependency}"
