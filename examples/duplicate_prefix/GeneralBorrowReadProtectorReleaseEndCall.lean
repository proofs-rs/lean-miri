import duplicate_prefix.GeneralBorrowReadProtectorRelease
import duplicate_prefix.GeneralBorrowReadProtectorRowWeakens
namespace DuplicatePrefix.GeneralBorrowReadProtectorReleaseEndCall
open Miri Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- Actual Read helper release. Its singleton endCall retains full Positive and runtime facts;
other protector lookups are exact, with no final-state premise. -/
theorem release_end_call (tree : BorrowTree) (global : GlobalState)
    (before : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (allocation : AllocId) (tag : BorTag) (anchor selected : UniIndex) (maximum : Option BorTag) (offset len : UInt64)
    (positive : GeneralBorrowReadRowRange.Positive tree global.protectedTags anchor selected maximum offset len)
    (node : TreeNode) (present : tree.nodeAt anchor = some node) (sameTag : node.tag = tag) (hidden : node.isExposed = false)
    (tagged : tree.indexOfTag tag = some anchor) (distinct : tree.roots.toList.Nodup)
    (order : ∀ valid : 0 < tree.roots.size, selected ≠ tree.roots[0] → GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (short : tree.nodes.size < 65536)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree anchor .Read offset (offset+len)) :
    let actual := tree.releaseProtector tag global.protectedTags
    let after := global.endCall (({} : FrameState).addProtector allocation tag)
    actual.status = .Released ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree after ∧
    Nonempty (GeneralBorrowReadRowRange.Positive actual.tree after.protectedTags
      anchor selected maximum offset len) ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin actual.tree anchor .Write offset (offset+len) ∧
    after.protectedTags.contains tag = false ∧
    (∀ query, query ≠ tag → after.protectedTags.get query = global.protectedTags.get query) ∧
    actual.tree = {tree with locations := actual.tree.locations} ∧ actual.tree.locations.size = tree.locations.size := by
  obtain ⟨done,runtime,⟨owner⟩,activity,frame,capacity⟩ := GeneralBorrowReadProtectorRelease.release tree global before
    tag anchor selected maximum offset len positive node present hidden tagged distinct order short active
  let actual := tree.releaseProtector tag global.protectedTags
  let after := global.endCall (({} : FrameState).addProtector allocation tag)
  have presentAfter : actual.tree.nodeAt anchor = some node := by
    have nodes := congrArg BorrowTree.nodes frame
    change actual.tree.nodes.get anchor = some node
    rw [nodes]
    exact present
  obtain ⟨runtimeAfter,absent,other⟩ := GeneralBorrowHiddenProtectorDropRuntime.end_call actual.tree global runtime
    allocation tag anchor node presentAfter sameTag hidden
  have sameExposed : ∀ index value, actual.tree.nodeAt index = some value → value.isExposed = true →
      after.protectedTags.contains value.tag = global.protectedTags.contains value.tag := by
    intro index value found exposed
    have different : value.tag ≠ tag := by
      intro tagged
      have first := runtime.formed.allocator.nodeTags index value found
      have second := runtime.formed.allocator.nodeTags anchor node presentAfter
      have sameTagNodes : value.tag = node.tag := tagged.trans sameTag.symm
      rw [sameTagNodes,second] at first
      have equal : index = anchor := (Option.some.inj first).symm
      subst index
      have equalNode := Option.some.inj (found.symm.trans presentAfter)
      subst value
      rw [hidden] at exposed
      contradiction
    unfold ProtectedTags.contains
    rw [other value.tag different]
  have ownerAfter := GeneralBorrowReadProtectorRowWeakens.positive actual.tree global.protectedTags after.protectedTags
    (GeneralBorrowRelease.end_call_weakens global _) sameExposed anchor selected maximum offset len owner
  exact ⟨done,runtimeAfter,ownerAfter,activity,absent,other,frame,capacity⟩
end DuplicatePrefix.GeneralBorrowReadProtectorReleaseEndCall
