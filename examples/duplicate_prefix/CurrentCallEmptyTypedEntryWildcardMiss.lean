import duplicate_prefix.CurrentCallEmptyTypedEntryInteger
import duplicate_prefix.S03WildcardMissArgumentCopy
import duplicate_prefix.CurrentCallEmptyReferenceValidation
import duplicate_prefix.CandidateCurrentLiveRuntime
import duplicate_prefix.ScopedFrame

/-! Actual unresolved wildcard empty argument copying. The internal miss
is supplied by finite raw Candidate classification, never by the final caller. -/
namespace DuplicatePrefix.CurrentCallEmptyTypedEntryWildcardMiss
open Miri Miri.ABI Miri.Memory Miri.Input Miri.Interpreter Miri.TreeBorrows
open CandidateStableCallOwnership CandidateCurrentJointCall CanonicalConfigFacts ActualReferenceContext
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- The original empty proposal derives the actual reference-copy action in
its temporary FnEntry scope. Only local/frame readiness is supplied; no source
allocation, source grant, resolver result or successful operation is assumed. -/
theorem copy_argument
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : Before) (tracker : MachineHooks.BorrowState) (address : UInt64)
    (place : MPlaceTy Provenance) (call : CallLoans) (data : Identities)
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker (.pointer (Pointer.new .wildcard (Size.ofBytes address))) 0 place call data)
    (miss : before.user.addresses.allocIdFromAddr address 0
      (GlobalAddressLiveErrorExclusion.lookup before.memory) = .ok none)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (localId : MIR.LocalId) (valid : localId < frame.locals.size) (old : Immediate Provenance)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some ActualReferenceMetadata.reference)
    (noClocks : frame.extra.dataRace = none) :
    let entered := ScopedFrame.entered before tracker .FnEntry
    let fresh := CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 ActualReferenceMetadata.reference).imm
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
      (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base (.pointer (Pointer.new .wildcard (Size.ofBytes address))) 0)
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
  have candidate := CurrentCallEmptyTypedEntryInteger.empty_candidate input
  change address ≠ 0 ∧ DuplicatePrefixEmptyReferenceInput.Wildcard
    (DuplicatePrefixCallSpecification.imageContext options before tracker) before.memory before.user.addresses at candidate
  have absent := DuplicatePrefixTypeCacheOrigins.slice_not_constructed
    before.user.payload.payload.user.types input.machine.settings.metadata input.machine.cacheOrigins
  exact S03WildcardMissArgumentCopy.copy_empty_argument options limits remaining span input.machine.settings.nullComparator
    input.machine.settings.preciseOff input.machine.settings.implicitOff input.machine.settings.debugOff
    dynamicFuel validationFuel dynamicEq validationEq frames frame (ScopedFrame.entered before tracker .FnEntry)
    localId old valid live cached noClocks input.machine.settings.ghostOff input.machine.settings.shallow
    address candidate.1 {tracker with retagMode := .FnEntry} rfl rfl
    (CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources)
    candidate.2.nonstrict miss input.machine.settings.metadata absent
    (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference).stackView (by simp)


end
end DuplicatePrefix.CurrentCallEmptyTypedEntryWildcardMiss

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.CurrentCallEmptyTypedEntryWildcardMiss.copy_argument] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "wildcard miss empty argument entry depends on unapproved axiom {dependency}"
