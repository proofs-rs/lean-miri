import duplicate_prefix.S02DisjointFnEntryTree
import duplicate_prefix.S02SameDestinationReadReady

namespace DuplicatePrefix.S02SameDestinationCurrent
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Every reference witness used by actual typed argument passing has the
same-allocation destination capability on its exact installed finalTree.
Only the approved contract and witness data are used. -/
theorem destination_positive_final_tree
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (same : id = input.contract.destination.id)
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
    (fresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Positive
      (GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra reference.tracker tag reference.offset len)
      (TypedRetagGeneric.protectedGlobal reference.tracker.global fresh).protectedTags
      input.contract.destination.source input.contract.destination.selectedRoot input.contract.destination.maximum
      input.contract.destination.offset 1) := by
  obtain ⟨sameId,raw,parentTag,offsetEq,lenEq,_source,_selected,_maximum,runtime⟩ :=
    S05ConcreteEntryBridge.from_positive id tag address len reference input.contract.runtime input.contract.resources
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
  have rawSeparation : raw.offset.toNat+raw.len.toNat ≤ input.contract.destination.offset.toNat ∨
      (input.contract.destination.offset+1).toNat ≤ raw.offset.toNat := by
    simpa only [offsetEq,lenEq] using separation
  have result := S02DisjointFnEntryTree.positive reference.entry.allocation.extra reference.tracker ({} : FrameState)
    reference.id runtime raw input.contract.destination.source input.contract.destination.selectedRoot
    input.contract.destination.maximum input.contract.destination.offset 1 rawSeparation registeredDestination
  rw [parentTag,offsetEq,lenEq] at result
  exact result

end
end DuplicatePrefix.S02SameDestinationCurrent

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02SameDestinationCurrent.destination_positive_final_tree) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
