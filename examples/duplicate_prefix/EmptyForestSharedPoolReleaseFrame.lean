import duplicate_prefix.EmptyForestSharedPoolNext

namespace DuplicatePrefix.EmptyForestSharedPoolReleaseFrame
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshNode DuplicatePrefix.GeneralBorrowFreshGraph DuplicatePrefix.GeneralBorrowFreshAnchor
open EmptyForestSharedPool
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] UniValMap.insert
variable {tree : BorrowTree} {parentTag tag : BorTag}

/-- Actual zero shared insertion, with either slot, preserves all old node
exposure flags through parent attachment and the real SIFA loop. -/
theorem old_node (input : Input tree parentTag tag) (query : UniIndex) (node : TreeNode)
    (present : tree.nodeAt query = some node) :
    ∃ next, input.after.nodeAt query = some next ∧ next.isExposed = node.isExposed := by
  have stage : ∃ next, input.stage.nodeAt query = some next ∧ next.isExposed = node.isExposed := by
    by_cases same : query = input.parent
    · subst query
      have equal : input.parentNode = node := Option.some.inj (input.present.symm.trans present)
      refine ⟨updatedParent input.parentNode input.index,?_,?_⟩
      · change ((tree.nodes.insert input.index (sharedNode tag input.parent)).insert input.parent
          (updatedParent input.parentNode input.index)).get input.parent = _
        exact GeneralBorrowFreshLocation.get_same _ _ _
      · simp only [updatedParent,equal]
    · have different : query ≠ input.index := by
        intro equal
        change tree.nodes.get query = some node at present
        rw [equal,input.vacant] at present
        cases present
      refine ⟨node,?_,rfl⟩
      change ((tree.nodes.insert input.index (sharedNode tag input.parent)).insert input.parent
        (updatedParent input.parentNode input.index)).get query = _
      rw [GeneralBorrowFreshLocation.get_other _ input.parent query _ same,
        GeneralBorrowFreshLocation.get_other _ input.index query _ different]
      exact present
  obtain ⟨middle,lookup,flag⟩ := stage
  obtain ⟨next,found,_,_,_,_,exposed⟩ := GeneralBorrowFreshMetadataChildSifa.node_fields
    input.stage input.parent .Read query middle lookup
  exact ⟨next,found,exposed.trans flag⟩

/-- Actual old-ROOT protector release after a further zero shared append/reuse,
using separate initial unmaterialized permission data. -/
theorem release (input : Input tree parentTag tag) (oldTag : BorTag) (query : UniIndex) (node : TreeNode)
    (tagged : tree.indexOfTag oldTag = some query) (present : tree.nodeAt query = some node)
    (unexposed : node.isExposed = false) (absent : GeneralBorrowFreshFutureClean.Clean tree query)
    (protections : ProtectedTags) : input.after.releaseProtector oldTag protections = ⟨input.after,.Released⟩ := by
  have taggedAfter : input.after.indexOfTag oldTag = some query := by
    unfold BorrowTree.indexOfTag
    rw [input.mapping_after]
    have different : tag ≠ oldTag := by
      intro equal
      subst oldTag
      simp only [BorrowTree.indexOfTag,UniKeyMap.get,GeneralBorrowTagMap.fresh_find tree.tagMapping tag input.fresh,Option.map_none] at tagged
      cases tagged
    exact (GeneralBorrowTagMap.pushed_get_old tree.tagMapping tag oldTag different input.index input.free).trans tagged
  obtain ⟨next,lookup,flag⟩ := old_node input query node present
  exact EmptyForestUnmaterializedRelease.release input.after oldTag query next taggedAfter lookup
    (flag.trans unexposed) (input.future_clean query absent) protections

end DuplicatePrefix.EmptyForestSharedPoolReleaseFrame
