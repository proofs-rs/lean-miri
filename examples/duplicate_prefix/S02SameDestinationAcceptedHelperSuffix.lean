import duplicate_prefix.GeneralBorrowParentTagInvariant
import duplicate_prefix.S02SameDestinationAcceptedHelperStage
import duplicate_prefix.S02SameDestinationAcceptedHelperPhase
import duplicate_prefix.S02SameDestinationAcceptedReleasePositive
import duplicate_prefix.S02DisjointReleasePositive
import duplicate_prefix.GeneralBorrowRawFnEntryOrder
import duplicate_prefix.GeneralBorrowRawFnEntryHidden
import duplicate_prefix.S02HiddenLeafActiveRelease
namespace DuplicatePrefix.S02SameDestinationAcceptedHelperSuffix
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
/-- The actual protected mutable helper, release and endCall retain a disjoint
return child's full capability and activity. -/
theorem destination (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawFnEntry.Input tree tracker.global)
    (stepRoom : tree.nodes.size+1 < 65536)
    (target selected : UniIndex) (maximum : Option BorTag) (lower width : UInt64)
    (outside : input.offset.toNat+input.len.toNat ≤ lower.toNat ∨ (lower+width).toNat ≤ input.offset.toNat)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree tracker.global.protectedTags (some target) (some selected) maximum lower width)
    (node : TreeNode) (present : tree.nodeAt target = some node)
    (leaf : node.children = #[]) (hidden : node.isExposed = false) (different : target ≠ input.parent)
    (activity : GeneralBorrowFreshActiveWithin.ActiveWithin tree target .Write lower (lower+width)) :
    let borrowed := GeneralBorrowRawFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len
    let held := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom) tracker.global.nextPointerTag
    let released := (borrowed.releaseProtector tracker.global.nextPointerTag held.protectedTags).tree
    let returned := held.endCall (({} : FrameState).addProtector allocation tracker.global.nextPointerTag)
    Nonempty (DuplicatePrefixBorrowAuthorization.Positive released returned.protectedTags (some target) (some selected) maximum lower width) ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin released target .Write lower (lower+width) ∧
    ∃ next, released.nodeAt target = some next ∧ next.tag = node.tag ∧ next.parent = node.parent ∧ next.children = #[] ∧ next.isExposed = false := by
  obtain ⟨_,_,_,registeredRuntime,⟨registeredPositive⟩,fresh⟩ :=
    GeneralBorrowFnEntryRegistration.prepare tree tracker.global {} allocation input.tagRoom runtime
      input.parent input.selected input.maximum input.offset input.len input.positive
  let registration := GeneralBorrowFnEntryRegistration.registered tracker.global {} allocation input.tagRoom
  obtain ⟨active,next,nextPresent,nextTag,nextParent,nextLeaf,nextHidden⟩ :=
    S02SameDestinationAcceptedHelperStage.stage tree registration.1 registeredRuntime
      input.parentTag tracker.global.nextPointerTag input.parent input.selected target input.maximum input.offset input.len
      registeredPositive input.tagged input.distinct input.order input.short fresh input.nodeRoom
      node present leaf hidden different lower (lower+width) activity
  let borrowed := GeneralBorrowRawFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len
  let held := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom) tracker.global.nextPointerTag
  have activeBorrowed : GeneralBorrowFreshActiveWithin.ActiveWithin borrowed target .Write lower (lower+width) := active
  have nextBorrowed : borrowed.nodeAt target = some next := nextPresent
  obtain ⟨borrowedRuntime,capacity,growth,roots,_heldTag,_framePush,_fresh,child,lookup,⟨childPositive⟩,childActive⟩ :=
    GeneralBorrowRawFnEntryResources.resources tree tracker {} allocation runtime input
  obtain ⟨hiddenChild,childNode,hiddenLookup,childPresent,childTag,childHidden⟩ :=
    GeneralBorrowRawFnEntryHidden.hidden tree tracker {} allocation runtime input
  have childEq : hiddenChild = child := Option.some.inj (hiddenLookup.symm.trans lookup)
  subst hiddenChild
  have other : target ≠ child := by
    intro same
    have targetAtChild : borrowed.nodeAt child = some next := by simpa only [same] using nextBorrowed
    have nodeEq : next = childNode := Option.some.inj (targetAtChild.symm.trans childPresent)
    have below := GeneralBorrowParentTagInvariant.parent_below_fresh tree tracker.global runtime target node present
    have tags : node.tag = tracker.global.nextPointerTag := nextTag.symm.trans ((congrArg TreeNode.tag nodeEq).trans childTag)
    rw [tags] at below
    have impossible := UInt64.lt_iff_toNat_lt.mp below
    omega
  have order := (GeneralBorrowRawFnEntryOrder.conditional tree tracker {} allocation runtime input stepRoom).1
  obtain ⟨destinationBefore⟩ := S02SameDestinationAcceptedHelperPhase.final_tree tree tracker {} allocation runtime input
    (some target) (some selected) maximum lower width outside positive
  have outsideRelease : (input.offset+input.len).toNat ≤ lower.toNat ∨ (lower+width).toNat ≤ input.offset.toNat := by
    rcases outside with left | right
    · exact Or.inl (Nat.le_trans (by rw [UInt64.toNat_add];exact Nat.mod_le _ _) left)
    · exact Or.inr right
  obtain ⟨releasedPositive⟩ := S02SameDestinationAcceptedReleasePositive.release borrowed held borrowedRuntime tracker.global.nextPointerTag
    child input.selected input.maximum input.offset input.len childPositive childNode childPresent childHidden lookup
    (by rw [roots];exact input.distinct) order (Nat.lt_of_le_of_lt growth stepRoom) childActive
    (some target) (some selected) maximum lower width outsideRelease destinationBefore
  have retained := S02HiddenLeafActiveRelease.release borrowed held borrowedRuntime
    tracker.global.nextPointerTag child input.selected input.maximum input.offset input.len childPositive childNode childPresent childHidden
    lookup (by rw [roots];exact input.distinct) order (Nat.lt_of_le_of_lt growth stepRoom) childActive
    target next nextBorrowed nextLeaf nextHidden other lower (lower+width) activeBorrowed
  obtain ⟨_done,releasedRuntime,_positive,_activity,frame,_capacity⟩ := GeneralBorrowBothProtectorRelease.release borrowed held borrowedRuntime
    tracker.global.nextPointerTag child input.selected input.maximum input.offset input.len childPositive childNode childPresent childHidden lookup
    (by rw [roots];exact input.distinct) order (Nat.lt_of_le_of_lt growth stepRoom) childActive
  have presentReleased : (borrowed.releaseProtector tracker.global.nextPointerTag held.protectedTags).tree.nodeAt child = some childNode := by
    rw [frame];exact childPresent
  have ended := S02DisjointReleasePositive.end_call _ held releasedRuntime allocation tracker.global.nextPointerTag child childNode
    presentReleased childTag childHidden (some target) (some selected) maximum lower width releasedPositive
  refine ⟨ended,retained,next,?_,nextTag,nextParent,nextLeaf,nextHidden⟩
  rw [frame];exact nextBorrowed
end
end DuplicatePrefix.S02SameDestinationAcceptedHelperSuffix
