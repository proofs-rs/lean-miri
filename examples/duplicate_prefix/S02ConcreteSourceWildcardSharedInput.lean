import duplicate_prefix.S02ConcreteSourceWildcardInstalledBothIdentity
import duplicate_prefix.S02ConcreteSourceWildcardSharedBounds
import duplicate_prefix.GeneralBorrowReadRowRange

namespace DuplicatePrefix.S02ConcreteSourceWildcardSharedInput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- The actual installed source protector has the raw Read input for the
shared-reference helper, with numeric margins derived from the call contract. -/
theorem at_installed
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
    (firstFresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615)
    (destination : DuplicatePrefixReturnPlaceInput.Input
      (GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
        reference.tracker firstFresh reference.id reference.entry tag reference.offset len) place)
    (secondFresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615)
    (tree : BorrowTree) (updated : Allocation Provenance BorrowTree)
    (sourcePacket : S02ConcreteSourceWildcardBothPacket.SourcePacket id tag address len reference
      (S04ProtectUninit.finished
        (GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
          reference.tracker firstFresh reference.id reference.entry tag reference.offset len)
        place destination #[]
        {(RootArgumentsTwo.result (PositiveRootArguments.firstDone
          (RawRootInvocation.root before place input.contract.model.noDataRace)
          (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
            (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
              (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
          ({} : FrameState) reference.id reference.tracker.global.nextPointerTag) count).frame with
          location := .unwinding ⟨601⟩}
        (({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag)
        secondFresh tree updated).machine) :
    let sourceTree := GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
      reference.tracker tag reference.offset len
    let tracker := TypedBorrowSteps.registeredTracker
      (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
      destination.tracker.global.nextPointerTag
    ∃ raw : GeneralBorrowRawShared.Input sourceTree tracker.global,
      raw.parentTag = reference.tracker.global.nextPointerTag ∧
      raw.parent = sourcePacket.child ∧ raw.selected = sourcePacket.raw.selected ∧
      raw.maximum = sourcePacket.raw.maximum ∧ raw.offset = reference.offset ∧ raw.len = len := by
  let sourceTree := GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
    reference.tracker tag reference.offset len
  let tracker := TypedBorrowSteps.registeredTracker
    (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
    destination.tracker.global.nextPointerTag
  obtain ⟨_positive,_nonnull,_signed,_bounds,_capacity,_short,room,tagRoom⟩ :=
    S02ConcreteSourceWildcardSharedBounds.at_installed id tag address len input reference
      firstFresh destination secondFresh
  have trackerEq : sourcePacket.tracker = tracker := Option.some.inj
    (sourcePacket.enabled.symm.trans (show
      (S04ProtectUninit.finished
        (GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
          reference.tracker firstFresh reference.id reference.entry tag reference.offset len)
        place destination #[] _ _ secondFresh tree updated).machine.borrowTracker = some tracker from rfl))
  have positive : DuplicatePrefixBorrowAuthorization.Positive sourceTree tracker.global.protectedTags
      (some sourcePacket.child) (some sourcePacket.raw.selected) sourcePacket.raw.maximum
      reference.offset len := by
    rw [←trackerEq]
    exact sourcePacket.positive
  let raw : GeneralBorrowRawShared.Input sourceTree tracker.global := {
    parentTag := reference.tracker.global.nextPointerTag
    parent := sourcePacket.child
    selected := sourcePacket.raw.selected
    maximum := sourcePacket.raw.maximum
    offset := reference.offset
    len := len
    tagged := sourcePacket.tagged
    positive := Classical.choice (GeneralBorrowReadRowRange.of_positive sourceTree
      tracker.global.protectedTags sourcePacket.child sourcePacket.raw.selected
      sourcePacket.raw.maximum reference.offset len positive)
    distinct := sourcePacket.distinct
    order := sourcePacket.order
    short := sourcePacket.short
    nodeRoom := by
      have h : sourceTree.nodes.size + 2 ≤ 4294967295 := by
        simpa [sourceTree,Allocation.setExtra,Allocation.mapExtra] using room
      omega
    tagRoom := by
      apply UInt64.lt_iff_toNat_lt.mpr
      change tracker.global.nextPointerTag.value.toNat < 18446744073709551615
      change tracker.global.nextPointerTag.value.toNat + 1 < 18446744073709551615 at tagRoom
      omega }
  exact ⟨raw,rfl,rfl,rfl,rfl,rfl,rfl⟩

end
end DuplicatePrefix.S02ConcreteSourceWildcardSharedInput

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02ConcreteSourceWildcardSharedInput.at_installed) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete-source wildcard shared-input dependency {dependency}"
