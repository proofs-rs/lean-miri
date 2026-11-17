import duplicate_prefix.GeneralBorrowGcLiveNode

namespace DuplicatePrefix.GeneralBorrowGcDfsStage
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcWalker DuplicatePrefix.GeneralBorrowGcGuardedFold
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

set_option autoImplicit false in
/-- Staged DFS data deliberately permit stale edges among completed nodes.
Unprocessed nodes still have their original complete metadata; every child of a
completed surviving node is also completed. This is stable during unary collapse,
before its parent's final kept-child rewrite restores reciprocal topology. -/
structure Stage (original : BorrowTree) (processed : List UniIndex) (current : BorrowTree) : Prop where
  outside : ∀ index, index ∉ processed → current.nodes.get index = original.nodes.get index
  closed : ∀ index ∈ processed, ∀ node, current.nodes.get index = some node →
    ∀ child ∈ node.children.toList, child ∈ processed

/-- Deleting a completed node leaves every unprocessed original node intact. -/
theorem remove (original tree : BorrowTree) (processed : List UniIndex) (index : UniIndex)
    (member : index ∈ processed) (stage : Stage original processed tree) :
    Stage original processed (source_remove_useless_node tree index).1 := by
  cases stored : tree.nodes.get index with
  | none => unfold_source_remove_useless_node;simpa only [stored,Id.run,pure] using stage
  | some node =>
    unfold_source_remove_useless_node
    simp only [stored,Id.run,pure]
    refine ⟨?_,?_⟩
    · intro query outside
      have different : query ≠ index := fun same => outside (same ▸ member)
      exact (GeneralBorrowSparseRemoval.remove_get_other tree.nodes index query different).trans (stage.outside query outside)
    · intro query processedQuery value present child childMember
      have different : query ≠ index := by
        intro same;subst query
        rw [GeneralBorrowFreshDeassignment.get_removed] at present
        cases present
      rw [GeneralBorrowSparseRemoval.remove_get_other tree.nodes index query different] at present
      exact stage.closed query processedQuery value present child childMember

/-- Reparenting a completed replacement does not change its completed children
or touch any unprocessed node. -/
theorem reparent (original tree : BorrowTree) (processed : List UniIndex) (index parent : UniIndex)
    (member : index ∈ processed) (node : TreeNode) (present : tree.nodes.get index = some node)
    (stage : Stage original processed tree) :
    Stage original processed {tree with nodes := tree.nodes.insert index {node with parent := some parent}} := by
  refine ⟨?_,?_⟩
  · intro query outside
    have different : query ≠ index := fun same => outside (same ▸ member)
    exact (GeneralBorrowNodeUpdate.insert_existing_get_other tree.nodes index query node _ present different).trans (stage.outside query outside)
  · intro query processedQuery value found child childMember
    by_cases same : query = index
    · subst query
      rw [GeneralBorrowNodeUpdate.insert_existing_get_same tree.nodes index node _ present] at found
      cases found
      exact stage.closed index member node present child childMember
    · rw [GeneralBorrowNodeUpdate.insert_existing_get_other tree.nodes index query node _ present same] at found
      exact stage.closed query processedQuery value found child childMember

/-- The real final child-list rewrite marks exactly its parent completed. All
kept replacements must already have completed; no reciprocal intermediate graph
or operation-success premise is required for this stage-data transition. -/
theorem finish (original tree : BorrowTree) (processed : List UniIndex) (index : UniIndex)
    (node : TreeNode) (present : tree.nodes.get index = some node) (kept : Array UniIndex)
    (children : ∀ child ∈ kept.toList, child ∈ processed) (stage : Stage original processed tree) :
    Stage original (index::processed) {tree with nodes := tree.nodes.insert index {node with children := kept}} := by
  refine ⟨?_,?_⟩
  · intro query outside
    have parts : query ≠ index ∧ query ∉ processed := by simpa only [List.mem_cons,not_or] using outside
    exact (GeneralBorrowNodeUpdate.insert_existing_get_other tree.nodes index query node _ present parts.1).trans (stage.outside query parts.2)
  · intro query processedQuery value found child childMember
    by_cases same : query = index
    · subst query
      rw [GeneralBorrowNodeUpdate.insert_existing_get_same tree.nodes index node _ present] at found
      cases found
      exact List.mem_cons_of_mem _ (children child childMember)
    · rw [GeneralBorrowNodeUpdate.insert_existing_get_other tree.nodes index query node _ present same] at found
      have oldMember : query ∈ processed := (List.mem_cons.mp processedQuery).resolve_left same
      exact List.mem_cons_of_mem _ (stage.closed query oldMember value found child childMember)
end DuplicatePrefix.GeneralBorrowGcDfsStage
