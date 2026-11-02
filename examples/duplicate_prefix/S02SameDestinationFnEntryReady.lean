import duplicate_prefix.S02DisjointFnEntryDestination
import duplicate_prefix.S02SameDestinationReadReady

namespace DuplicatePrefix.S02SameDestinationFnEntryReady
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.MIR Miri.Interpreter
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- From only the approved call contract, same-allocation concrete source
FnEntry really completes and retains the general destination's full Positive
capability after its Read, physical constructor and actual ancestor SIFA. -/
theorem destination_positive_after_fn_entry
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (same : id = input.contract.destination.id) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
      (raw : GeneralBorrowRawFnEntry.Input reference.entry.allocation.extra reference.tracker.global)
      (output : GeneralBorrowForestFnEntry.Output),
      reference.id = id ∧ raw.parentTag = tag ∧ raw.offset = reference.offset ∧ raw.len = len ∧
      DuplicatePrefixBorrowContract.RuntimeFacts reference.entry.allocation.extra reference.tracker.global ∧
      GeneralBorrowForestFnEntry.operation reference.entry.allocation.extra reference.tracker.global
        ({} : FrameState) reference.id tag reference.offset len .VisitChildrenOfAccessed = .ok output ∧
      output.global = (GeneralBorrowFnEntryRegistration.registered reference.tracker.global
        ({} : FrameState) reference.id raw.tagRoom).1 ∧
      output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive output.child.tree output.global.protectedTags
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
  obtain ⟨output,actual,global,read,child,destination⟩ := S02DisjointFnEntryDestination.invoke
    reference.entry.allocation.extra reference.tracker.global ({} : FrameState) reference.id runtime raw
    input.contract.destination.source input.contract.destination.selectedRoot input.contract.destination.maximum
    input.contract.destination.offset 1 rawSeparation registeredDestination
  refine ⟨reference,raw,output,sameId.symm,parentTag,offsetEq,lenEq,runtime,?_,global,read,child,destination⟩
  simpa only [parentTag,offsetEq,lenEq] using actual

end
end DuplicatePrefix.S02SameDestinationFnEntryReady

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02SameDestinationFnEntryReady.destination_positive_after_fn_entry) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
