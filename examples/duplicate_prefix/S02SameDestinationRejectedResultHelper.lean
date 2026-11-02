import duplicate_prefix.S02SameDestinationRejectedResultSharedStage
import duplicate_prefix.S02SameDestinationRejectedResultReadRelease
import duplicate_prefix.GeneralBorrowParentTagInvariant
import duplicate_prefix.GeneralBorrowSharedLenHelperGraph
namespace DuplicatePrefix.S02SameDestinationRejectedResultHelper
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
noncomputable section
/-- The literal shared length-helper construction and real release preserve a
previous hidden leaf's activity and leaf metadata. -/
theorem helper (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawSharedFnEntry.Input tree tracker.global)
    (stepRoom : tree.nodes.size+1 < 65536)
    (target : UniIndex) (node : TreeNode) (present : tree.nodeAt target = some node)
    (leaf : node.children = #[]) (hidden : node.isExposed = false) (different : target ≠ input.parent)
    (lower upper : UInt64) (activity : GeneralBorrowFreshActiveWithin.ActiveWithin tree target .Write lower upper) :
    GeneralBorrowFreshActiveWithin.ActiveWithin (GeneralBorrowSharedLenHelperGraph.releasedTree tree tracker input)
      target .Write lower upper ∧
    ∃ next, (GeneralBorrowSharedLenHelperGraph.releasedTree tree tracker input).nodeAt target = some next ∧
      next.tag = node.tag ∧ next.parent = node.parent ∧ next.children = #[] ∧ next.isExposed = false := by
  obtain ⟨_,_,_,registeredRuntime,⟨registeredPositive⟩,fresh⟩ :=
    GeneralBorrowFnEntryReadRegistration.prepare tree tracker.global {} allocation input.tagRoom runtime
      input.parent input.selected input.maximum input.offset input.len input.positive
  let registration := GeneralBorrowFnEntryRegistration.registered tracker.global {} allocation input.tagRoom
  obtain ⟨active,next,nextPresent,nextTag,nextParent,nextLeaf,nextHidden⟩ :=
    S02SameDestinationRejectedResultSharedStage.stage tree registration.1 registeredRuntime
      input.parentTag tracker.global.nextPointerTag input.parent input.selected target input.maximum input.offset input.len
      registeredPositive input.tagged input.distinct input.order input.short fresh input.nodeRoom true
      node present leaf hidden different lower upper activity
  let borrowed := GeneralBorrowRawSharedFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len
  let held := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom) tracker.global.nextPointerTag
  have activeBorrowed : GeneralBorrowFreshActiveWithin.ActiveWithin borrowed target .Write lower upper := active
  have nextBorrowed : borrowed.nodeAt target = some next := nextPresent
  obtain ⟨borrowedRuntime,capacity,growth,roots,_heldTag,_fresh,child,lookup,⟨parentPositive⟩,⟨childPositive⟩,childActive⟩ :=
    GeneralBorrowRawSharedFnEntryResources.resources tree tracker {} allocation runtime input
  obtain ⟨graphChild,graphLookup,⟨childNode,childPresent,childTag,childParent,childHidden⟩,oldNodes⟩ :=
    GeneralBorrowRawSharedFnEntryGraph.graph tree tracker {} allocation runtime input
  have childEq : graphChild = child := Option.some.inj (graphLookup.symm.trans lookup)
  subst graphChild
  have other : target ≠ child := by
    intro same
    have targetAtChild : borrowed.nodeAt child = some next := by simpa [same] using nextBorrowed
    have nodeEq : next = childNode := Option.some.inj (targetAtChild.symm.trans childPresent)
    have below := GeneralBorrowParentTagInvariant.parent_below_fresh tree tracker.global runtime target node present
    have tags : node.tag = tracker.global.nextPointerTag := nextTag.symm.trans ((congrArg TreeNode.tag nodeEq).trans childTag)
    rw [tags] at below
    have impossible := UInt64.lt_iff_toNat_lt.mp below
    omega
  have preserved := S02SameDestinationRejectedResultReadRelease.release borrowed held borrowedRuntime
    tracker.global.nextPointerTag child input.selected input.maximum input.offset input.len childPositive
    childNode childPresent childHidden lookup (by rw [roots];exact input.distinct)
    (GeneralBorrowRawSharedFnEntryOrder.order tree tracker {} allocation runtime input)
    (Nat.lt_of_le_of_lt growth stepRoom) childActive target next nextBorrowed nextLeaf nextHidden other lower upper activeBorrowed
  obtain ⟨_done,_runtime,_positive,_activity,frame,_capacity⟩ := GeneralBorrowReadProtectorRelease.release borrowed held borrowedRuntime
    tracker.global.nextPointerTag child input.selected input.maximum input.offset input.len childPositive
    childNode childPresent childHidden lookup (by rw [roots];exact input.distinct)
    (GeneralBorrowRawSharedFnEntryOrder.order tree tracker {} allocation runtime input)
    (Nat.lt_of_le_of_lt growth stepRoom) childActive
  refine ⟨?_,next,?_,nextTag,nextParent,nextLeaf,nextHidden⟩
  · rw [GeneralBorrowSharedLenHelperGraph.releasedTree_eq]
    exact preserved
  · rw [GeneralBorrowSharedLenHelperGraph.releasedTree_eq]
    change (borrowed.releaseProtector tracker.global.nextPointerTag held.protectedTags).tree.nodeAt target = some next
    rw [frame]
    exact nextBorrowed
end
end DuplicatePrefix.S02SameDestinationRejectedResultHelper
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SameDestinationRejectedResultHelper.helper) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved literal helper activity dependency {dependency}"
