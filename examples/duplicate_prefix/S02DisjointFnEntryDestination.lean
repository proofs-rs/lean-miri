import duplicate_prefix.S02DisjointMutableRuntime
import duplicate_prefix.S02DisjointReadPositive
import duplicate_prefix.GeneralBorrowRawFnEntry

namespace DuplicatePrefix.S02DisjointFnEntryDestination
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixBorrowAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- The actual registered FnEntry Read and mutable constructor preserve a
disjoint destination in the same allocation. Arbitrary destination provenance,
source component and cutoff are retained; operation successes are conclusions. -/
theorem invoke (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (input : GeneralBorrowRawFnEntry.Input tree global)
    (source selected : Option UniIndex) (maximum : Option BorTag) (lower width : UInt64)
    (outside : input.offset.toNat+input.len.toNat ≤ lower.toNat ∨ (lower+width).toNat ≤ input.offset.toNat)
    (destination : Positive tree
      (GeneralBorrowFnEntryRegistration.registered global frame allocation input.tagRoom).1.protectedTags
      source selected maximum lower width) :
    ∃ output, GeneralBorrowForestFnEntry.operation tree global frame allocation input.parentTag input.offset input.len
        .VisitChildrenOfAccessed = .ok output ∧
      output.global = (GeneralBorrowFnEntryRegistration.registered global frame allocation input.tagRoom).1 ∧
      output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      Nonempty (Positive output.child.tree output.global.protectedTags source selected maximum lower width) := by
  obtain ⟨allocated,held,frameEq,registeredRuntime,⟨registeredPositive⟩,fresh⟩ :=
    GeneralBorrowFnEntryRegistration.prepare tree global frame allocation input.tagRoom runtime
      input.parent input.selected input.maximum input.offset input.len input.positive
  let registration := GeneralBorrowFnEntryRegistration.registered global frame allocation input.tagRoom
  let accessed := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset)
    (Size.ofBytes input.len) .Read registration.1.protectedTags .VisitChildrenOfAccessed
  obtain ⟨contract,afterRuntime,⟨afterPositive⟩⟩ := GeneralBorrowConcreteRowReadRange.access_runtime tree registration.1 registeredRuntime
    input.parentTag input.parent input.selected input.maximum input.tagged (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .VisitChildrenOfAccessed input.offset input.len registeredPositive input.distinct input.order input.short
    (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨afterDestination⟩ := S02DisjointReadPositive.positive_from_source_contract tree input.parentTag input.parent input.selected input.maximum
    input.tagged (Size.ofBytes input.offset) (Size.ofBytes input.len) registration.1.protectedTags .VisitChildrenOfAccessed
    source selected maximum lower width destination runtime.formed.well input.positive.bounds outside contract
  obtain ⟨parentNode,parentPresent⟩ := afterPositive.sourcePresent input.parent rfl
  have tagged : accessed.tree.indexOfTag input.parentTag = some input.parent := by
    unfold BorrowTree.indexOfTag
    rw [contract.tags]
    exact input.tagged
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping global.nextPointerTag := by rw [contract.tags];exact fresh
  have room : accessed.tree.nodes.size+1 ≤ 4294967295 := by rw [contract.nodes];exact input.nodeRoom
  have nonzero : input.len ≠ 0 := by
    intro zero
    have positive := input.positive.positive
    rw [zero] at positive
    contradiction
  obtain ⟨childDone,childDestination⟩ := S02DisjointMutableRuntime.construct accessed.tree registration.1 afterRuntime
    input.parentTag global.nextPointerTag input.parent parentNode tagged parentPresent freshAfter room input.offset input.len nonzero
    afterPositive.bounds source selected maximum lower width outside afterDestination
  let output : GeneralBorrowForestFnEntry.Output := ⟨registration.1,registration.2,global.nextPointerTag,accessed,
    accessed.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true⟩
  refine ⟨output,?_,rfl,contract.completed,childDone,childDestination⟩
  simp only [GeneralBorrowForestFnEntry.operation,allocated,Except.bind,Except.pure,bind,pure]
  rfl

end DuplicatePrefix.S02DisjointFnEntryDestination

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02DisjointFnEntryDestination.invoke) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
