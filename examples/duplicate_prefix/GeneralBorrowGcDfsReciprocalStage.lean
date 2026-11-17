import duplicate_prefix.GeneralBorrowGcDfsStage

namespace DuplicatePrefix.GeneralBorrowGcDfsReciprocalStage
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Only completed surviving parents have repaired child lists. Unprocessed
parents may retain stale original child arrays while their child fold runs.
Unlike the earlier Stage.closed, this records actual child lookup/parent edges. -/
structure Reciprocal (processed : List UniIndex) (tree : BorrowTree) : Prop where
  children : ∀ index ∈ processed, ∀ node, tree.nodes.get index = some node →
    ∀ child ∈ node.children.toList, ∃ childNode,
      tree.nodes.get child = some childNode ∧ childNode.parent = some index
  distinct : ∀ index ∈ processed, ∀ node, tree.nodes.get index = some node → node.children.toList.Nodup

theorem initial (tree : BorrowTree) : Reciprocal [] tree := by
  constructor <;> intro index member <;> simp at member

/-- Removing a completed child cannot damage any completed parent's repaired
list when the child's own parent is still unprocessed. The unprocessed parent's
stale original edge is intentionally allowed. -/
theorem remove (tree : BorrowTree) (processed : List UniIndex) (index parent : UniIndex)
    (node : TreeNode) (present : tree.nodes.get index = some node) (edge : node.parent = some parent)
    (pending : parent ∉ processed) (good : Reciprocal processed tree) :
    Reciprocal processed (source_remove_useless_node tree index).1 := by
  unfold_source_remove_useless_node
  simp only [present,Id.run,pure]
  constructor
  · intro query member value found child inChildren
    have queryDifferent : query ≠ index := by
      intro same;subst query;rw [GeneralBorrowFreshDeassignment.get_removed] at found;cases found
    rw [GeneralBorrowSparseRemoval.remove_get_other tree.nodes index query queryDifferent] at found
    obtain ⟨childNode,childPresent,childParent⟩ := good.children query member value found child inChildren
    have childDifferent : child ≠ index := by
      intro same;subst child
      have equal := Option.some.inj (present.symm.trans childPresent)
      subst childNode
      have equal := Option.some.inj (edge.symm.trans childParent)
      exact pending (equal ▸ member)
    exact ⟨childNode,(GeneralBorrowSparseRemoval.remove_get_other tree.nodes index child childDifferent).trans childPresent,childParent⟩
  · intro query member value found
    have queryDifferent : query ≠ index := by
      intro same;subst query;rw [GeneralBorrowFreshDeassignment.get_removed] at found;cases found
    rw [GeneralBorrowSparseRemoval.remove_get_other tree.nodes index query queryDifferent] at found
    exact good.distinct query member value found

/-- Reparenting a retained replacement after its old parent was removed preserves
all already repaired child lists: no surviving completed parent can still claim
that replacement under the old, now absent parent index. -/
theorem reparent (tree : BorrowTree) (processed : List UniIndex) (index oldParent parent : UniIndex)
    (node : TreeNode) (present : tree.nodes.get index = some node) (edge : node.parent = some oldParent)
    (removed : tree.nodes.get oldParent = none) (good : Reciprocal processed tree) :
    Reciprocal processed {tree with nodes := tree.nodes.insert index {node with parent := some parent}} := by
  have noClaim : ∀ query ∈ processed, ∀ value, tree.nodes.get query = some value → index ∉ value.children.toList := by
    intro query member value found claimed
    obtain ⟨childNode,childPresent,childParent⟩ := good.children query member value found index claimed
    have equal := Option.some.inj (present.symm.trans childPresent)
    subst childNode
    have same : oldParent = query := Option.some.inj (edge.symm.trans childParent)
    rw [same,found] at removed
    cases removed
  constructor
  · intro query member value found child inChildren
    by_cases same : query = index
    · subst query
      rw [GeneralBorrowNodeUpdate.insert_existing_get_same tree.nodes index node _ present] at found
      cases found
      have different : child ≠ index := by intro equal;subst child;exact noClaim index member node present inChildren
      obtain ⟨childNode,childPresent,childParent⟩ := good.children index member node present child inChildren
      exact ⟨childNode,(GeneralBorrowNodeUpdate.insert_existing_get_other tree.nodes index child node _ present different).trans childPresent,childParent⟩
    · rw [GeneralBorrowNodeUpdate.insert_existing_get_other tree.nodes index query node _ present same] at found
      have different : child ≠ index := by intro equal;subst child;exact noClaim query member value found inChildren
      obtain ⟨childNode,childPresent,childParent⟩ := good.children query member value found child inChildren
      exact ⟨childNode,(GeneralBorrowNodeUpdate.insert_existing_get_other tree.nodes index child node _ present different).trans childPresent,childParent⟩
  · intro query member value found
    by_cases same : query = index
    · subst query
      rw [GeneralBorrowNodeUpdate.insert_existing_get_same tree.nodes index node _ present] at found
      cases found
      exact good.distinct index member node present
    · rw [GeneralBorrowNodeUpdate.insert_existing_get_other tree.nodes index query node _ present same] at found
      exact good.distinct query member value found

/-- Final source child-list rewrite establishes repaired reciprocity for the
newly completed parent. Its kept children supply real current parent edges;
other completed parents retain their own repaired lists. -/
theorem finish (tree : BorrowTree) (processed : List UniIndex) (index : UniIndex)
    (node : TreeNode) (present : tree.nodes.get index = some node) (kept : Array UniIndex)
    (distinct : kept.toList.Nodup)
    (children : ∀ child ∈ kept.toList, ∃ childNode, tree.nodes.get child = some childNode ∧ childNode.parent = some index)
    (good : Reciprocal processed tree) :
    Reciprocal (index::processed) {tree with nodes := tree.nodes.insert index {node with children := kept}} := by
  have transfer : ∀ child childNode, tree.nodes.get child = some childNode →
      ∃ next, (tree.nodes.insert index {node with children := kept}).get child = some next ∧ next.parent = childNode.parent := by
    intro child childNode found
    by_cases same : child = index
    · subst child
      have equal := Option.some.inj (present.symm.trans found)
      subst childNode
      exact ⟨_,GeneralBorrowNodeUpdate.insert_existing_get_same tree.nodes index node _ present,rfl⟩
    · exact ⟨childNode,(GeneralBorrowNodeUpdate.insert_existing_get_other tree.nodes index child node _ present same).trans found,rfl⟩
  constructor
  · intro query member value found child inChildren
    by_cases same : query = index
    · subst query
      rw [GeneralBorrowNodeUpdate.insert_existing_get_same tree.nodes index node _ present] at found
      cases found
      obtain ⟨childNode,childPresent,childParent⟩ := children child inChildren
      obtain ⟨next,nextPresent,nextParent⟩ := transfer child childNode childPresent
      exact ⟨next,nextPresent,nextParent.trans childParent⟩
    · rw [GeneralBorrowNodeUpdate.insert_existing_get_other tree.nodes index query node _ present same] at found
      have earlier : query ∈ processed := (List.mem_cons.mp member).resolve_left same
      obtain ⟨childNode,childPresent,childParent⟩ := good.children query earlier value found child inChildren
      obtain ⟨next,nextPresent,nextParent⟩ := transfer child childNode childPresent
      exact ⟨next,nextPresent,nextParent.trans childParent⟩
  · intro query member value found
    by_cases same : query = index
    · subst query
      rw [GeneralBorrowNodeUpdate.insert_existing_get_same tree.nodes index node _ present] at found
      cases found
      exact distinct
    · rw [GeneralBorrowNodeUpdate.insert_existing_get_other tree.nodes index query node _ present same] at found
      exact good.distinct query ((List.mem_cons.mp member).resolve_left same) value found

end DuplicatePrefix.GeneralBorrowGcDfsReciprocalStage
