import duplicate_prefix.GeneralBorrowGcDfsIncomingRemove

namespace DuplicatePrefix.GeneralBorrowGcDfsIncomingCollapse
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcDfsIncoming
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def collapsed (tree : BorrowTree) (index replacement parent : UniIndex) (replacementNode : TreeNode) : BorrowTree :=
  {(source_remove_useless_node tree index).1 with nodes :=
    (source_remove_useless_node tree index).1.nodes.insert replacement {replacementNode with parent := some parent}}

/-- Atomic source unary collapse removes an old completed parent and reparents
its UNIQUE incoming child. Temporary dangling pointers between these source
primitives are not claimed to satisfy the completed-parent invariant. -/
theorem preserves (original tree : BorrowTree) (processed : List UniIndex) (parent index replacement : UniIndex)
    (items : List UniIndex) (kept : Array UniIndex) (node replacementNode : TreeNode)
    (present : tree.nodes.get index = some node) (single : node.children.toList = [replacement])
    (replacementPresent : tree.nodes.get replacement = some replacementNode) (different : replacement ≠ index)
    (pending : parent ∉ processed) (good : Active original processed parent (index::items) kept tree) :
    Active original processed parent items (kept.push replacement) (collapsed tree index replacement parent replacementNode) := by
  have afterPresent := (GeneralBorrowGcDfsIncomingRemove.other tree index replacement node present different).trans replacementPresent
  have inverse : ∀ child value, (collapsed tree index replacement parent replacementNode).nodes.get child = some value →
      (child = replacement ∧ value = {replacementNode with parent := some parent}) ∨
      (child ≠ replacement ∧ child ≠ index ∧ tree.nodes.get child = some value) := by
    intro child value found
    simp only [collapsed] at found
    by_cases same : child = replacement
    · subst child
      rw [GeneralBorrowNodeUpdate.insert_existing_get_same _ replacement replacementNode _ afterPresent] at found
      exact .inl ⟨rfl,Option.some.inj found.symm⟩
    · rw [GeneralBorrowNodeUpdate.insert_existing_get_other _ replacement child replacementNode _ afterPresent same] at found
      have before := GeneralBorrowGcDfsIncomingRemove.inverse tree index child node value present found
      exact .inr ⟨same,before.1,before.2⟩
  have transfer : ∀ query value, query ≠ index → tree.nodes.get query = some value →
      ∃ after, (collapsed tree index replacement parent replacementNode).nodes.get query = some after ∧ after.children = value.children := by
    intro query value outside found
    by_cases same : query = replacement
    · subst query
      have equal := Option.some.inj (replacementPresent.symm.trans found)
      subst value
      exact ⟨_,GeneralBorrowNodeUpdate.insert_existing_get_same _ replacement replacementNode _ afterPresent,rfl⟩
    · refine ⟨value,?_,rfl⟩
      simp only [collapsed]
      rw [GeneralBorrowNodeUpdate.insert_existing_get_other _ replacement query replacementNode _ afterPresent same]
      exact (GeneralBorrowGcDfsIncomingRemove.other tree index query node present outside).trans found
  constructor
  · intro child value found otherParent edge completed
    rcases inverse child value found with ⟨same,valueEq⟩ | ⟨notReplacement,notIndex,before⟩
    · subst child;subst value
      have equal : parent = otherParent := Option.some.inj edge
      exact False.elim (pending (equal ▸ completed))
    · obtain ⟨parentNode,parentPresent,member⟩ := good.completed child value before otherParent edge completed
      have outside : otherParent ≠ index := by
        intro same;subst otherParent
        have equal := Option.some.inj (present.symm.trans parentPresent)
        subst parentNode
        rw [single] at member
        exact notReplacement (by simpa using member)
      obtain ⟨after,afterPresent,childrenEq⟩ := transfer otherParent parentNode outside parentPresent
      exact ⟨after,afterPresent,by rw [childrenEq];exact member⟩
  · intro child value found otherParent edge outside
    rcases inverse child value found with ⟨same,valueEq⟩ | ⟨notReplacement,notIndex,before⟩
    · subst child;subst value
      have equal : parent = otherParent := Option.some.inj edge
      exact False.elim (outside (List.mem_cons.mpr (.inl equal.symm)))
    · exact good.unprocessed child value before otherParent edge outside
  · intro child value found
    rcases inverse child value found with ⟨same,valueEq⟩ | ⟨notReplacement,notIndex,before⟩
    · subst child;exact good.origins replacement replacementNode replacementPresent
    · exact good.origins child value before
  · intro child value found edge
    rcases inverse child value found with ⟨same,valueEq⟩ | ⟨notReplacement,notIndex,before⟩
    · subst child
      exact List.mem_append_left _ (by simp)
    · have covered := good.frontier child value before edge
      rcases List.mem_append.mp covered with keptMember | remaining
      · exact List.mem_append_left _ (by rw [Array.toList_push];exact List.mem_append_left _ keptMember)
      · exact List.mem_append_right _ ((List.mem_cons.mp remaining).resolve_left notIndex)

end DuplicatePrefix.GeneralBorrowGcDfsIncomingCollapse
