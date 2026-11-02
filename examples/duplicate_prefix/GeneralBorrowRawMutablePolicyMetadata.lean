import duplicate_prefix.GeneralBorrowRawDefaultResources
import duplicate_prefix.GeneralBorrowRawFnEntryOrder
import duplicate_prefix.GeneralBorrowRawFnEntryResources
import duplicate_prefix.GeneralBorrowRawMutableParentRestore
namespace DuplicatePrefix.GeneralBorrowRawMutablePolicyMetadata
open Miri Miri.Memory Miri.ABI Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- The exact helper graph inherits only the original CONDITIONAL order and
explicit two-child headroom, with arbitrary coherent allocator reuse. -/
theorem metadata (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawDefault.Input tree tracker.global)
    (headroom : tree.nodes.size+2 < 65536)
    (tagsRoom : tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615) :
    let defaultTree := (GeneralBorrowRawDefaultExpression.child tree tracker.global.protectedTags
      input.parentTag tracker.global.nextPointerTag input.offset input.len .VisitChildrenOfAccessed).tree
    let allocated := ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom
    let helperTree := GeneralBorrowRawFnEntryArgument.finalTree defaultTree allocated tracker.global.nextPointerTag input.offset input.len
    helperTree.roots.toList.Nodup ∧ helperTree.nodes.size < 65536 ∧
    (∀ valid : 0 < helperTree.roots.size, input.selected ≠ helperTree.roots[0] → GeneralBorrowWildcardParentTagOrder.ParentTagOrder helperTree) := by
  let defaultTree := (GeneralBorrowRawDefaultExpression.child tree tracker.global.protectedTags
    input.parentTag tracker.global.nextPointerTag input.offset input.len .VisitChildrenOfAccessed).tree
  let allocated := ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom
  have first := GeneralBorrowRawDefaultResources.resources tree tracker runtime input headroom tagsRoom
  dsimp only at first
  obtain ⟨defaultRuntime,_,defaultRoom,next,nextTag,nextSelected,nextMaximum,nextOffset,nextLen⟩ := first
  have second := GeneralBorrowRawFnEntryResources.resources defaultTree allocated {} allocation defaultRuntime next
  dsimp only at second
  rw [nextTag,nextOffset,nextLen] at second
  obtain ⟨_,_,_,roots,_,_,_,_⟩ := second
  have order := GeneralBorrowRawFnEntryOrder.conditional defaultTree allocated {} allocation defaultRuntime next defaultRoom
  dsimp only at order
  rw [nextTag,nextOffset,nextLen,nextSelected] at order
  refine ⟨?_,order.2,order.1⟩
  rw [roots]
  exact next.distinct

/-- Actual release/Read/Write retain the exact root array on both outcomes. -/
theorem copy_roots (packet : GeneralBorrowRawAsMutToCopy.Input) :
    let released := (packet.entry.allocation.extra.releaseProtector packet.tag packet.tracker.global.protectedTags).tree
    let read := released.performBorrowAccessRange (.concrete packet.tag) (Size.ofBytes packet.offset) (Size.ofBytes packet.count)
      .Read (GeneralBorrowRawAsMutToCopy.held packet).global.protectedTags .VisitChildrenOfAccessed
    let write := read.tree.performBorrowAccessRange (.concrete packet.tag) (Size.ofBytes (packet.offset+packet.count)) (Size.ofBytes packet.count)
      .Write (GeneralBorrowRawAsMutToCopy.held packet).global.protectedTags .VisitChildrenOfAccessed
    write.tree.roots = packet.entry.allocation.extra.roots := by
  obtain ⟨input,_,_,_⟩ := GeneralBorrowRawAsMutCopyResources.copy_input packet
  have operations := GeneralBorrowRawCopyInput.accesses _ _ _ _ _ _ input
  have releaseFrame := GeneralBorrowStructuralReleaseGeometryFrame.release packet.entry.allocation.extra packet.tracker.global.protectedTags packet.tag
  have releaseRoots := congrArg BorrowTree.roots releaseFrame
  exact operations.2.1.roots.trans (operations.1.roots.trans releaseRoots)
end DuplicatePrefix.GeneralBorrowRawMutablePolicyMetadata
