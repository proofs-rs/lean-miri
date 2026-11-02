import duplicate_prefix.GeneralBorrowRawWildcardFnEntryScopedResources
import duplicate_prefix.GeneralBorrowFreshActiveWithinAccess
import duplicate_prefix.S04ReturnWildcardRelease

namespace DuplicatePrefix.S04ReturnWildcardLifecycle
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- The actual wildcard protection tree operations, concrete uninitializing
Write, return-protector release and endCall restore the original wildcard
destination permission. Every permission premise describes the INITIAL tree.

This is the borrow-tree lifecycle with an initially empty callee protector
frame. It is not the MIR body or physical-memory store theorem: later hidden
argument protectors are handled by `release_to_wildcard` once their scoped
capability transport is connected. -/
theorem invoke (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (offset : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags none none none offset 1)
    (distinct : tree.roots.toList.Nodup) (short : tree.nodes.size+1 < 65536)
    (nodeRoom : tree.nodes.size+1 ≤ 4294967295)
    (tagRoom : global.nextPointerTag.value < 18446744073709551615)
    (emptyFrame : frame.protectedTags = #[]) :
    ∃ output, GeneralBorrowRawWildcardFnEntryRuntime.operation tree global frame allocation offset 1 = .ok output ∧
      output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      let written := output.child.tree.performBorrowAccessRange (.concrete output.tag)
        (Size.ofBytes offset) (Size.ofBytes 1) .Write output.global.protectedTags .VisitChildrenOfAccessed
      written.status = .Completed ∧
      let released := written.tree.releaseProtector output.tag output.global.protectedTags
      released.status = .Released ∧
      DuplicatePrefixBorrowContract.RuntimeFacts released.tree (output.global.endCall output.frame) ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive released.tree
        (output.global.endCall output.frame).protectedTags none none none offset 1) := by
  obtain ⟨output,actual,outputTag,outputGlobal,frameEq,readDone,childDone,childRuntime,capacity,growth,
    childDistinct,child,tagged,roots,⟨childPositive⟩,childActive,node,present,nodeTag,parentless,leaf,hidden⟩ :=
    GeneralBorrowRawWildcardFnEntryScopedResources.invoke tree global frame allocation runtime offset 1 positive distinct
      (by omega) nodeRoom tagRoom
  let written := output.child.tree.performBorrowAccessRange (.concrete output.tag)
    (Size.ofBytes offset) (Size.ofBytes 1) .Write output.global.protectedTags .VisitChildrenOfAccessed
  obtain ⟨writeContract,writeRuntime,⟨writePositive⟩⟩ := GeneralBorrowFreshRootScopedRange.access_runtime_kind
    output.child.tree output.global childRuntime output.tag child child output.tag tagged
    (Size.ofBytes offset) (Size.ofBytes 1) .Write .VisitChildrenOfAccessed offset 1 childPositive childDistinct
    (by omega) (Nat.le_refl _) (Nat.le_refl _)
  have writePresent : written.tree.nodeAt child = some node := by
    change written.tree.nodes.get child = some node
    rw [writeContract.nodes]
    exact present
  have writeTagged : written.tree.indexOfTag output.tag = some child := by
    unfold BorrowTree.indexOfTag
    rw [writeContract.tags]
    exact tagged
  have writeDistinct : written.tree.roots.toList.Nodup := by rw [writeContract.roots];exact childDistinct
  have writeActive := GeneralBorrowFreshActiveWithinAccess.normal output.child.tree output.tag
    (Size.ofBytes offset) (Size.ofBytes 1) .Write output.global.protectedTags .VisitChildrenOfAccessed
    child offset (offset+1) childRuntime.formed.well childPositive.base.bounds
    (Nat.le_refl _) (Nat.le_refl _) childActive
  have owned : (allocation,output.tag) ∈ output.frame.protectedTags.toList := by
    rw [frameEq,emptyFrame]
    simp
  have hiddenFrame : S04ReturnReleaseParent.HiddenFrame written.tree output.frame := by
    intro row member index value found sameTag
    have same : row = (allocation,output.tag) := by simpa only [frameEq,emptyFrame,Array.toList_push,Array.toList_empty,List.nil_append,List.mem_singleton] using member
    subst row
    have lookup := writeRuntime.formed.allocator.nodeTags index value found
    rw [sameTag] at lookup
    have sameIndex : index = child := Option.some.inj (lookup.symm.trans writeTagged)
    subst index
    have sameNode : value = node := Option.some.inj (found.symm.trans writePresent)
    subst value
    exact hidden
  have nonempty : 0 < tree.roots.size := positive.wildcardRoot rfl
  have notPrimary : ∀ valid : 0 < written.tree.roots.size, written.tree.roots[0] ≠ child := by
    intro valid same
    have before : output.child.tree.roots[0]'(by rw [roots,Array.size_push];omega) = child := by
      have rootsEq : written.tree.roots = output.child.tree.roots := writeContract.roots
      simpa only [rootsEq] using same
    have rootAt : tree.roots[0]'nonempty = child := by
      simpa only [roots,Array.getElem_push_lt nonempty] using before
    have member : child ∈ tree.roots.toList := by
      rw [←rootAt]
      exact Array.mem_toList_iff.mpr (Array.getElem_mem nonempty)
    have nodup := childDistinct
    rw [roots,Array.toList_push,List.nodup_append] at nodup
    exact nodup.2.2 child member child (by simp) rfl
  obtain ⟨releaseDone,finalRuntime,finalPositive,shape,finalCapacity⟩ := S04ReturnWildcardRelease.release_to_wildcard
    written.tree output.global output.frame writeRuntime allocation output.tag child offset 1 writePositive node writePresent
    nodeTag parentless leaf hidden writeTagged owned hiddenFrame notPrimary writeDistinct (by rw [writeContract.nodes];omega) writeActive
  exact ⟨output,actual,readDone,childDone,writeContract.completed,releaseDone,finalRuntime,finalPositive⟩

end DuplicatePrefix.S04ReturnWildcardLifecycle
