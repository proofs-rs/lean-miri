import duplicate_prefix.ActualReferenceMetadata

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace DuplicatePrefix.ActualEmptyReference
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter
open CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata

theorem validate (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (cmp : ProjectionMetadataFacts.NullComparator)
    (precise : options.retag.preciseInteriorMut = false)
    (implicitWrites : options.retag.implicitWrites = false)
    (debug : options.place.debugAssertions = false)
    (dynamicFuel validationFuel : Nat) (dynamicFuelEq : options.place.dynamicFuel = dynamicFuel + 1)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (address : UInt64) (nonzero : address ≠ 0)
    (live : frame.locals[localId].value = .live (.immediate (RetagReferencePlace.integerSliceValue address 0 reference).imm))
    (cached : frame.locals[localId].layout = some reference)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    ValidityMachine.validateRuntime (config options remaining span).validity () (validationFuel + 1)
      (LocalPlaces.localRuntimePlace frames.size frame localId reference) true
      (Storage.withCurrent frames frame machine) =
      .ok () (TypedRetagEmpty.afterTag (Storage.withCurrent frames frame machine) tracker fresh) := by
  obtain ⟨ctx⟩ := exists_context options remaining span precise implicitWrites
  have fields := actual_fields options () remaining span
  obtain ⟨target, tail, inhabit, name, kind⟩ := visitor_metadata options remaining span
  obtain ⟨width, pointerSize⟩ := visitor_target options remaining span
  obtain ⟨pa, pb, ra, rb, offset, repr⟩ := reference_repr
  have debugInner : ctx.inner.debugAssertions = false := ctx.innerDebug.trans (fields.debug.trans debug)
  have noDebug := congrFun (congrFun (fields.debugAbiNoChecks debug)
    (RetagReferencePlace.integerSliceValue address 0 reference).imm) reference
  rw [← ctx.innerAbi] at noDebug
  have sizing : (adapted options remaining span ctx.pointers).sizeAndAlign
      (RetagReferencePlace.integerSlicePlace address 0 pointee)
      (Storage.withCurrent frames frame {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}) =
      .ok (some (Size.ZERO, Align.ONE))
      (Storage.withCurrent frames frame {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}) := by
    rw [← ctx.visitor.sizing]
    exact ProjectionMetadataFacts.actual_validity_size_at options remaining span cmp
      (Storage.withCurrent frames frame {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}})
      dynamicFuel dynamicFuelEq 0 metadata notConstructed (by decide)
      (RetagReferencePlace.integerSlicePlace address 0 pointee) rfl rfl
  apply RootEmptyReferenceValidity.empty_validate_at_from_fields
    (config options remaining span).validity (config options remaining span).access
    (config options remaining span).allocation ctx.inner (adapted options remaining span ctx.pointers)
    ReferenceMetadataFacts.prepared ctx.pointers () options.limits.retag ctx.visitor ctx.source
    reference pointee address nonzero (reference_queries options remaining span ctx.pointers)
    _ _ ProjectionMetadataFacts.slice_layout_shape.2.2 ctx.pointer
    (actual_target_width options () remaining span) width pointerSize
    ProjectionMetadataFacts.slice_layout_shape.2.1 _ _ "&mut [u8]" validationFuel _ _
    frames frame machine localId valid live cached reference_sized pa pb ra rb offset repr debugInner noDebug
    ghost shallow (actual_retain_touched options () remaining span) tracker enabled mode fresh sizing
  · rw [reference_ty, pointee_ty]; exact RootMetadataQueries.mutable_slice_dereference
  · rw [pointee_ty]; exact pointee_layout
  · rw [pointee_ty]; exact tail
  · rw [pointee_ty]; exact inhabit
  · rw [reference_ty]; exact name
  · rw [reference_ty]; exact kind

end DuplicatePrefix.ActualEmptyReference
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.ActualEmptyReference.validate) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved actual empty reference dependency {dependency}"
