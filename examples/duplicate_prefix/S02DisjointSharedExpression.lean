import duplicate_prefix.S02DisjointSharedRuntime
import duplicate_prefix.S02DisjointReadOnlyPositive
import duplicate_prefix.GeneralBorrowRawSharedExpression

namespace DuplicatePrefix.S02DisjointSharedExpression
open Miri Miri.Memory Miri.ABI Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixBorrowAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- Actual unprotected shared-expression tag allocation, Read, Frozen child
and Read SIFA retain an arbitrary disjoint full destination capability. -/
theorem literal (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (input : GeneralBorrowRawShared.Input tree global)
    (source selected : Option UniIndex) (maximum : Option BorTag) (lower width : UInt64)
    (outside : input.offset.toNat+input.len.toNat ≤ lower.toNat ∨ (lower+width).toNat ≤ input.offset.toNat)
    (destination : Positive tree global.protectedTags source selected maximum lower width) :
    let advanced := GeneralBorrowFnEntryRegistration.advanced global input.tagRoom
    let read := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len)
      .Read advanced.protectedTags .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshAnchor.sharedState) .Frozen false
    GeneralBorrowRawShared.operation tree global input.parentTag input.offset input.len .VisitChildrenOfAccessed =
      .ok ⟨advanced,global.nextPointerTag,read,child⟩ ∧ read.status = .Completed ∧ child.outcome = .ok () ∧
    Nonempty (Positive child.tree global.protectedTags source selected maximum lower width) := by
  obtain ⟨allocated,registeredRuntime,⟨registeredPositive⟩,fresh,_unheld⟩ := GeneralBorrowReadTagAllocation.prepare tree global input.tagRoom
    runtime input.parent input.selected input.maximum input.offset input.len input.positive
  let advanced := GeneralBorrowFnEntryRegistration.advanced global input.tagRoom
  let accessed := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .Read advanced.protectedTags .VisitChildrenOfAccessed
  obtain ⟨contract,afterRuntime,⟨afterPositive⟩⟩ := GeneralBorrowReadRowRange.access tree advanced registeredRuntime
    input.parentTag input.parent input.selected input.maximum input.tagged (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .VisitChildrenOfAccessed input.offset input.len registeredPositive input.distinct input.order input.short (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨afterDestination⟩ := S02DisjointReadOnlyPositive.positive_from_source_contract tree input.parentTag input.parent input.selected input.maximum
    input.tagged (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read advanced.protectedTags .VisitChildrenOfAccessed
    source selected maximum lower width destination runtime.formed.well input.positive.bounds outside contract.capacity
  obtain ⟨parentNode,parentPresent⟩ := afterPositive.sourcePresent
  have tagged : accessed.tree.indexOfTag input.parentTag = some input.parent := by
    unfold BorrowTree.indexOfTag
    rw [contract.tags]
    exact input.tagged
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping global.nextPointerTag := by rw [contract.tags];exact fresh
  have room : accessed.tree.nodes.size+1 ≤ 4294967295 := by rw [contract.nodes];exact input.nodeRoom
  have nonzero : input.len ≠ 0 := by intro zero;have positive := input.positive.positive;rw [zero] at positive;contradiction
  obtain ⟨childDone,positive⟩ := S02DisjointSharedRuntime.construct accessed.tree advanced afterRuntime input.parentTag global.nextPointerTag
    input.parent parentNode tagged parentPresent freshAfter room false input.offset input.len nonzero afterPositive.bounds
    source selected maximum lower width outside afterDestination
  refine ⟨?_,contract.completed,childDone,positive⟩
  simp only [GeneralBorrowRawShared.operation,allocated,Except.bind,Except.pure,bind,pure]

end DuplicatePrefix.S02DisjointSharedExpression

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02DisjointSharedExpression.literal) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
