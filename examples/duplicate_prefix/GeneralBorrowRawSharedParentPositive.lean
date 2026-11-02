import duplicate_prefix.GeneralBorrowSharedParentPositive
import duplicate_prefix.GeneralBorrowRawSharedExpression
import duplicate_prefix.GeneralBorrowDefaultTagAllocation
import duplicate_prefix.GeneralBorrowConcreteRowReadRange
import duplicate_prefix.GeneralBorrowSharedChildGraph
import duplicate_prefix.GeneralBorrowRawTargetActivity
namespace DuplicatePrefix.GeneralBorrowRawSharedParentPositive
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
/-- The actual shared-expression tree retains its ORIGINAL mutable parent's
FULL Positive and activity from current Both data. The fresh shared temporary
is derived hidden, unprotected and directly parented by that mutable owner.
Neither successor permissions nor constructor success are premises. -/
theorem literal (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (input : GeneralBorrowRawShared.Input tree global)
    (both : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags
      (some input.parent) (some input.selected) input.maximum input.offset input.len)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree input.parent .Write input.offset (input.offset+input.len)) :
    let actual := GeneralBorrowRawSharedExpression.child tree global.protectedTags input.parentTag global.nextPointerTag
      input.offset input.len .VisitChildrenOfAccessed
    let advanced := GeneralBorrowFnEntryRegistration.advanced global input.tagRoom
    DuplicatePrefixBorrowContract.RuntimeFacts actual.tree advanced ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Positive actual.tree advanced.protectedTags
      (some input.parent) (some input.selected) input.maximum input.offset input.len) ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin actual.tree input.parent .Write input.offset (input.offset+input.len) ∧
    ∃ temporary tempNode observerNode, actual.tree.indexOfTag global.nextPointerTag = some temporary ∧
      actual.tree.nodeAt temporary = some tempNode ∧ tempNode.tag = global.nextPointerTag ∧
      tempNode.parent = some input.parent ∧ tempNode.isExposed = false ∧
      advanced.protectedTags.contains tempNode.tag = false ∧ actual.tree.nodeAt input.parent = some observerNode := by
  obtain ⟨allocated,advancedRuntime,⟨advancedBoth⟩,fresh,unheld⟩ := GeneralBorrowDefaultTagAllocation.prepare tree global input.tagRoom runtime
    input.parent input.selected input.maximum input.offset input.len both
  let advanced := GeneralBorrowFnEntryRegistration.advanced global input.tagRoom
  let accessed := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .Read advanced.protectedTags .VisitChildrenOfAccessed
  obtain ⟨contract,afterReadRuntime,⟨afterReadBoth⟩⟩ := GeneralBorrowConcreteRowReadRange.access_runtime tree advanced advancedRuntime
    input.parentTag input.parent input.selected input.maximum input.tagged (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .VisitChildrenOfAccessed input.offset input.len advancedBoth input.distinct input.order input.short (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨parentNode,parentPresent⟩ := afterReadBoth.sourcePresent input.parent rfl
  have tagged : accessed.tree.indexOfTag input.parentTag = some input.parent := by
    unfold BorrowTree.indexOfTag
    rw [contract.tags]
    exact input.tagged
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping global.nextPointerTag := by rw [contract.tags];exact fresh
  have room : accessed.tree.nodes.size+1 ≤ 4294967295 := by rw [contract.nodes];exact input.nodeRoom
  have bound : global.nextPointerTag.value.toNat < advanced.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value global.nextPointerTag input.tagRoom
    change global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag global.nextPointerTag input.tagRoom).value.toNat
    omega
  have nonzero : input.len ≠ 0 := by intro zero;have h:=both.positive;rw [zero] at h;contradiction
  obtain ⟨done,afterRuntime,capacity,growth,child,lookup,roots,⟨parentBoth⟩⟩ :=
    GeneralBorrowSharedParentPositive.construct accessed.tree advanced afterReadRuntime input.parentTag global.nextPointerTag input.parent parentNode
      tagged parentPresent freshAfter room bound unheld input.selected input.maximum input.offset input.len afterReadBoth
  have readActivity : GeneralBorrowFreshActiveWithin.ActiveWithin accessed.tree input.parent .Write input.offset (input.offset+input.len) :=
    GeneralBorrowFreshActiveWithinAccess.normal tree input.parentTag (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read
      advanced.protectedTags .VisitChildrenOfAccessed input.parent input.offset (input.offset+input.len)
      runtime.formed.well both.bounds (Nat.le_refl _) (Nat.le_refl _) active
  have afterActivity := GeneralBorrowRawTargetActivity.shared accessed.tree advanced afterReadRuntime input.parentTag global.nextPointerTag
    input.parent parentNode tagged parentPresent freshAfter room false input.offset input.len nonzero afterReadBoth.bounds
    input.parent input.offset (input.offset+input.len) (Nat.le_refl _) (Nat.le_refl _) readActivity
  obtain ⟨graphChild,graphLookup,⟨tempNode,tempPresent,tempTag,tempParent,tempHidden⟩,oldNodes⟩ :=
    GeneralBorrowSharedChildGraph.construct accessed.tree advanced afterReadRuntime input.parentTag global.nextPointerTag input.parent parentNode
      tagged parentPresent freshAfter room false input.offset input.len nonzero afterReadBoth.bounds
  have equal : graphChild = child := Option.some.inj (graphLookup.symm.trans lookup)
  subst graphChild
  obtain ⟨observerNode,observerPresent⟩ := parentBoth.sourcePresent input.parent rfl
  exact ⟨afterRuntime,⟨parentBoth⟩,afterActivity,child,tempNode,observerNode,lookup,tempPresent,tempTag,tempParent,tempHidden,
    by simpa only [tempTag,GeneralBorrowFnEntryRegistration.advanced] using unheld,observerPresent⟩
end DuplicatePrefix.GeneralBorrowRawSharedParentPositive
