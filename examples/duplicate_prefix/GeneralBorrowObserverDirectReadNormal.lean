import duplicate_prefix.GeneralBorrowObserverReadDirectParent
import duplicate_prefix.GeneralBorrowObserverReadRestore
namespace DuplicatePrefix.GeneralBorrowObserverDirectReadNormal
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Normal Read through the current unprotected shared temporary preserves its
mutable direct parent's Both table under the REAL protector list, including a
fresh Strong tag registered for the next child while absent from the tree. -/
theorem access (tree : BorrowTree) (location : LocationTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (source observer : UniIndex) (sourceNode : TreeNode)
    (present : tree.nodeAt source = some sourceNode) (edge : sourceNode.parent = some observer)
    (hidden : sourceNode.isExposed = false) (unprotected : global.protectedTags.contains sourceNode.tag = false)
    (sourceRead : DuplicatePrefixNormalKind.Capability tree location global.protectedTags source .Read)
    (observerBoth : DuplicatePrefixBorrowAuthorization.Normal tree location global.protectedTags observer)
    (mode : ChildrenVisitMode) :
    (tree.performNormalAccessAt location source .Read global.protectedTags mode).access.status = .Completed ∧
    (tree.performNormalAccessAt location source .Read global.protectedTags mode).outcome = .ok () ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree
      (tree.performNormalAccessAt location source .Read global.protectedTags mode).location global.protectedTags observer) := by
  let allocation : AllocId := ⟨1,by decide⟩
  have same : (global.endCall (({} : FrameState).addProtector allocation sourceNode.tag)).protectedTags = global.protectedTags := by
    simpa only [GlobalState.endCall,FrameState.addProtector,Array.foldl_push,Array.foldl_empty] using
      GeneralBorrowObserverReadRestore.remove_absent global.protectedTags sourceNode.tag unprotected
  have initial : DuplicatePrefixBorrowAuthorization.Normal tree location
      (global.endCall (({} : FrameState).addProtector allocation sourceNode.tag)).protectedTags observer := by
    rw [same]
    exact observerBoth
  obtain ⟨done,outcome,next,sameComponent⟩ := GeneralBorrowObserverReadDirectParent.access tree location global runtime allocation
    source observer sourceNode present edge hidden sourceRead initial runtime.formed.fits mode
  refine ⟨done,outcome,?_⟩
  rw [same] at next
  exact ⟨next⟩
end DuplicatePrefix.GeneralBorrowObserverDirectReadNormal
