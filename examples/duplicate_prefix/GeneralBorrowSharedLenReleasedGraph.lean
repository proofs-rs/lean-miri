import duplicate_prefix.GeneralBorrowRawSharedFnEntryGraph
import duplicate_prefix.GeneralBorrowRawSharedFnEntryOrder
import duplicate_prefix.GeneralBorrowStructuralReleaseGeometryFrame
namespace DuplicatePrefix.GeneralBorrowSharedLenReleasedGraph
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Exact helper released-tree graph ledger, including every outcome of real
release. All metadata follow from the initial raw shared call input and actual
constructor; no final tag/node/order premise is supplied. -/
theorem ledger (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawSharedFnEntry.Input tree tracker.global)
    (stepRoom : tree.nodes.size+1 < 65536) :
    let borrowed := GeneralBorrowRawSharedFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len
    let held := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom) tracker.global.nextPointerTag
    let released := (borrowed.releaseProtector tracker.global.nextPointerTag held.global.protectedTags).tree
    released.roots = tree.roots ∧ released.nodes.size ≤ tree.nodes.size+1 ∧ released.nodes.size < 65536 ∧
      released.roots.toList.Nodup ∧
      (∀ valid : 0 < released.roots.size, input.selected ≠ released.roots[0] → GeneralBorrowWildcardParentTagOrder.ParentTagOrder released) ∧
      (∀ query oldNode, tree.nodeAt query = some oldNode →
        ∃ next, released.nodeAt query = some next ∧ next.tag = oldNode.tag ∧ next.parent = oldNode.parent ∧ next.isExposed = oldNode.isExposed) := by
  let borrowed := GeneralBorrowRawSharedFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len
  let held := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom) tracker.global.nextPointerTag
  let released := (borrowed.releaseProtector tracker.global.nextPointerTag held.global.protectedTags).tree
  have releaseFrame : released = {borrowed with locations := released.locations} :=
    GeneralBorrowStructuralReleaseGeometryFrame.release borrowed held.global.protectedTags tracker.global.nextPointerTag
  obtain ⟨_,_,growth,roots,_⟩ := GeneralBorrowRawSharedFnEntryResources.resources tree tracker frame allocation runtime input
  have releasedRoots : released.roots = tree.roots := by rw [releaseFrame];exact roots
  have releasedGrowth : released.nodes.size ≤ tree.nodes.size+1 := by rw [releaseFrame];exact growth
  refine ⟨releasedRoots,releasedGrowth,Nat.lt_of_le_of_lt releasedGrowth stepRoom,?_,?_,?_⟩
  · rw [releasedRoots];exact input.distinct
  · change ∀ valid : 0 < released.roots.size, input.selected ≠ released.roots[0] → GeneralBorrowWildcardParentTagOrder.ParentTagOrder released
    have ordered := GeneralBorrowRawSharedFnEntryOrder.order tree tracker frame allocation runtime input
    have nodeFrame : released.nodes = borrowed.nodes := by simpa only using congrArg BorrowTree.nodes releaseFrame
    have rootFrame : released.roots = borrowed.roots := by simpa only using congrArg BorrowTree.roots releaseFrame
    simpa only [GeneralBorrowWildcardParentTagOrder.ParentTagOrder,nodeFrame,rootFrame] using ordered
  · intro query oldNode present
    obtain ⟨_,_,_,oldNodes⟩ := GeneralBorrowRawSharedFnEntryGraph.graph tree tracker frame allocation runtime input
    obtain ⟨next,found,tag,parent,hidden⟩ := oldNodes query oldNode present
    exact ⟨next,by change released.nodeAt query = some next;rw [releaseFrame];exact found,tag,parent,hidden⟩
end DuplicatePrefix.GeneralBorrowSharedLenReleasedGraph
