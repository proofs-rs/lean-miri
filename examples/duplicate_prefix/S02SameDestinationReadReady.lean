import duplicate_prefix.S02DisjointReadPositive
import duplicate_prefix.S02SameDestinationLiveTransport
import duplicate_prefix.S02SeparateDestinationAuthorization

namespace DuplicatePrefix.S02SameDestinationReadReady
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.MIR Miri.Interpreter
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- From the current call contract, the actual FnEntry source Read retains
the same-allocation destination's positive borrow authorization at its
disjoint byte. The child constructor follows this Read and is still open. -/
theorem destination_positive_after_read
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (same : id = input.contract.destination.id) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
      (raw : GeneralBorrowRawFnEntry.Input reference.entry.allocation.extra reference.tracker.global),
      let registered := GeneralBorrowFnEntryRegistration.registered reference.tracker.global
        ({} : FrameState) reference.id raw.tagRoom
      let read := reference.entry.allocation.extra.performBorrowAccessRange
        (.concrete tag) (Size.ofBytes reference.offset) (Size.ofBytes len) .Read
        registered.1.protectedTags .VisitChildrenOfAccessed
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive read.tree registered.1.protectedTags
        input.contract.destination.source input.contract.destination.selectedRoot
        input.contract.destination.maximum input.contract.destination.offset 1) := by
  obtain ⟨reference,sameId,raw,parentTag,offsetEq,lenEq,_,_,_,runtime⟩ :=
    S05ConcreteEntryBridge.from_contract id tag address len input.contract nonempty
  have disjoint := S02SameDestinationLiveTransport.actual_reference_disjoint
    id tag address len input nonempty same reference
  have trackerEq : reference.tracker = input.contract.tracker :=
    Option.some.inj (reference.enabled.symm.trans input.contract.runtime.enabled)
  have room : input.contract.tracker.global.nextPointerTag.value < 18446744073709551615 := by
    simpa only [←trackerEq] using raw.tagRoom
  obtain ⟨destination⟩ := S02SeparateDestinationAuthorization.destination_positive_after_registration input room
  have registeredDestination : DuplicatePrefixBorrowAuthorization.Positive
      reference.entry.allocation.extra
      (GeneralBorrowFnEntryRegistration.registered reference.tracker.global
        ({} : FrameState) reference.id raw.tagRoom).1.protectedTags
      input.contract.destination.source input.contract.destination.selectedRoot
      input.contract.destination.maximum input.contract.destination.offset 1 := by
    have entryEq : reference.entry = input.contract.destination.entry := by
      have live := reference.live
      have destId : reference.id = input.contract.destination.id := sameId.symm.trans same
      rw [destId] at live
      exact congrArg Prod.snd (Option.some.inj (live.symm.trans input.contract.destination.live))
    have treeEq : reference.entry.allocation.extra = input.contract.destination.entry.allocation.extra :=
      congrArg (fun entry : LocalAllocation Provenance BorrowTree MiriMemoryKind => entry.allocation.extra) entryEq
    have direct : DuplicatePrefixBorrowAuthorization.Positive
        input.contract.destination.entry.allocation.extra
        (GeneralBorrowFnEntryRegistration.registered reference.tracker.global
          ({} : FrameState) reference.id raw.tagRoom).1.protectedTags
        input.contract.destination.source input.contract.destination.selectedRoot
        input.contract.destination.maximum input.contract.destination.offset 1 := by
      simpa only [trackerEq,GeneralBorrowFnEntryRegistration.registered,
        GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector,
        TypedRetagGeneric.protectedGlobal,TypedRetagGeneric.allocatedGlobal]
        using destination
    simpa only [treeEq] using direct
  obtain ⟨_,_,_,registeredRuntime,⟨sourcePositive⟩,_⟩ :=
    GeneralBorrowFnEntryRegistration.prepare reference.entry.allocation.extra reference.tracker.global
      ({} : FrameState) reference.id raw.tagRoom runtime raw.parent raw.selected raw.maximum
      raw.offset raw.len raw.positive
  let registered := GeneralBorrowFnEntryRegistration.registered reference.tracker.global
    ({} : FrameState) reference.id raw.tagRoom
  have sourceContract := (GeneralBorrowConcreteRowReadRange.access_runtime
    reference.entry.allocation.extra registered.1 registeredRuntime tag raw.parent raw.selected raw.maximum
    (by simpa only [parentTag] using raw.tagged)
    (Size.ofBytes reference.offset) (Size.ofBytes len) .VisitChildrenOfAccessed
    reference.offset len (by simpa only [offsetEq,lenEq] using sourcePositive)
    raw.distinct raw.order raw.short (Nat.le_refl _) (Nat.le_refl _)).1
  refine ⟨reference,raw,?_⟩
  have bound := reference.borrow.bounds
  have destBound := input.contract.destination.borrow.bounds
  have targetFits : (input.contract.destination.offset+1).toNat =
      input.contract.destination.offset.toNat+1 := by
    simp only [UInt64.toNat_add,UInt64.toNat_one]
    apply Nat.mod_eq_of_lt
    have capacity := input.contract.destination.borrow.bounds
    have limit := input.contract.destination.entry.allocation.extra.locations.size.bytes.toNat_lt
    have one : UInt64.toNat 1 = 1 := by decide
    rw [one] at capacity
    omega
  have separation : reference.offset.toNat+len.toNat ≤ input.contract.destination.offset.toNat ∨
      (input.contract.destination.offset+1).toNat ≤ reference.offset.toNat := by
    rcases disjoint with left | right
    · exact Or.inl left
    · exact Or.inr (by rw [targetFits];exact right)
  exact S02DisjointReadPositive.positive_from_source_contract
    reference.entry.allocation.extra tag raw.parent raw.selected raw.maximum
    (by simpa only [parentTag] using raw.tagged)
    (Size.ofBytes reference.offset) (Size.ofBytes len) registered.1.protectedTags
    .VisitChildrenOfAccessed input.contract.destination.source input.contract.destination.selectedRoot
    input.contract.destination.maximum input.contract.destination.offset 1
    registeredDestination runtime.formed.well (by change reference.offset.toNat+len.toNat ≤ _;exact bound)
    separation (by change GeneralBorrowConcreteRowReadRange.Contract _ _ _ _ _ _ _ _;exact sourceContract)

end
end DuplicatePrefix.S02SameDestinationReadReady

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02SameDestinationReadReady.destination_positive_after_read) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
