import duplicate_prefix.CurrentCallAdmission
import duplicate_prefix.CurrentCallEmptyReferenceValidation
import duplicate_prefix.CandidateCurrentLiveRuntime
import duplicate_prefix.ScopedFrame

/-! Actual integer-encoded empty argument copying from the original proposed
input. A dangling nonnull address needs no source allocation, loan or origin.
This is an entry component, not a whole-call or ordinary-coverage theorem. -/
namespace DuplicatePrefix.CurrentCallEmptyTypedEntryInteger
open Miri Miri.ABI Miri.Memory Miri.Input Miri.Interpreter Miri.TreeBorrows
open CandidateStableCallOwnership CandidateCurrentJointCall CanonicalConfigFacts ActualReferenceContext
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Empty source storage supplies exactly the original provenance-sensitive
Candidate; the positive-storage alternative is impossible at zero length. -/
theorem empty_candidate {options limits remaining span before tracker argument place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data) :
    DuplicatePrefixEmptyReferenceInput.Candidate
      (DuplicatePrefixCallSpecification.imageContext options before tracker) before.memory before.user.addresses
      (DuplicatePrefixSliceArgument.placePointer argument) := by
  rcases input.actual.sourceValue with empty | positive
  · exact empty.2
  · exact False.elim (positive.1 rfl)

/-- The original empty proposal derives the actual reference-copy action in
its temporary FnEntry scope. Only local/frame readiness is supplied; no source
allocation, source grant, resolver result or successful operation is assumed. -/
theorem copy_argument
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : Before) (tracker : MachineHooks.BorrowState) (address : UInt64)
    (place : MPlaceTy Provenance) (call : CallLoans) (data : Identities)
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker (.integer address) 0 place call data)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (localId : MIR.LocalId) (valid : localId < frame.locals.size) (old : Immediate Provenance)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some ActualReferenceMetadata.reference)
    (noClocks : frame.extra.dataRace = none) :
    let entered := ScopedFrame.entered before tracker .FnEntry
    let fresh := CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources
    let value := (RetagReferencePlace.integerSliceValue address 0 ActualReferenceMetadata.reference).imm
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
      (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base (.integer address) 0)
      (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference).stackView
      (Storage.withCurrent frames frame entered) =
      .ok () (TypedRetagEmpty.afterTag
        (Storage.withCurrent frames (CurrentCallEmptyReferenceValidation.writtenFrame frame localId valid value) entered)
        {tracker with retagMode := .FnEntry} fresh) := by
  dsimp only
  have workPositive : 0 < DuplicatePrefixCallSpecification.work before 0 := by
    unfold DuplicatePrefixCallSpecification.work
    omega
  have dynamicPositive : 0 < options.place.dynamicFuel :=
    Nat.lt_of_lt_of_le workPositive input.machine.resources.dynamicFuel
  have validationPositive : 0 < options.limits.validation :=
    Nat.lt_of_lt_of_le workPositive input.machine.resources.configuredFuel.2.2.2
  let dynamicFuel := options.place.dynamicFuel-1
  let validationFuel := options.limits.validation-1
  have dynamicEq : options.place.dynamicFuel = dynamicFuel+1 := by dsimp only [dynamicFuel]; omega
  have validationEq : options.limits.validation = validationFuel+1 := by dsimp only [validationFuel]; omega
  have nonzero : address ≠ 0 := by
    simpa only [DuplicatePrefixSliceArgument.placePointer, DuplicatePrefixEmptyReferenceInput.Candidate,
      Pointer.withoutProvenance, Pointer.new, Size.ofBytes, true_and, and_true] using empty_candidate input
  have absent := DuplicatePrefixTypeCacheOrigins.slice_not_constructed
    before.user.payload.payload.user.types input.machine.settings.metadata input.machine.cacheOrigins
  exact ReferenceArgumentCopy.copy_empty_argument options limits remaining span input.machine.settings.nullComparator
    input.machine.settings.preciseOff input.machine.settings.implicitOff input.machine.settings.debugOff
    dynamicFuel validationFuel dynamicEq validationEq frames frame (ScopedFrame.entered before tracker .FnEntry)
    localId old valid live cached noClocks input.machine.settings.ghostOff input.machine.settings.shallow
    address nonzero {tracker with retagMode := .FnEntry} rfl rfl
    (CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources)
    input.machine.settings.metadata absent
    (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference).stackView (by simp)

/-- The zero-size integer FnEntry changes only the tag allocator. In
particular it creates no protector or source-tree mutation. -/
theorem afterTag_frame {K U : Type} (frames : Array CompilerFrameContext.ActualFrame)
    (frame : CompilerFrameContext.ActualFrame) (before : MachineHooks.MachineState K U)
    (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615) :
    (TypedRetagEmpty.afterTag (Storage.withCurrent frames frame before) tracker fresh).stack.frames = frames.push frame ∧
    (TypedRetagEmpty.afterTag (Storage.withCurrent frames frame before) tracker fresh).machine.memory = before.memory ∧
    (TypedRetagEmpty.afterTag (Storage.withCurrent frames frame before) tracker fresh).machine.user = before.user := by
  exact ⟨rfl,rfl,rfl⟩

end
end DuplicatePrefix.CurrentCallEmptyTypedEntryInteger

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.CurrentCallEmptyTypedEntryInteger.copy_argument,
      ``DuplicatePrefix.CurrentCallEmptyTypedEntryInteger.afterTag_frame] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "integer empty argument entry depends on unapproved axiom {dependency}"
