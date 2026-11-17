import duplicate_prefix.GeneralBorrowGcDfsStage

namespace DuplicatePrefix.GeneralBorrowGcStrictChildren
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcWalker
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Strict original ranks on current child edges survive stale references.
Present endpoints are not required on the child side during postorder surgery. -/
def Ranked (rank : UniIndex → Nat) (tree : BorrowTree) : Prop :=
  ∀ index node, tree.nodes.get index = some node →
    ∀ child ∈ node.children.toList, rank index < rank child

theorem remove (rank : UniIndex → Nat) (tree : BorrowTree) (index : UniIndex) (ranked : Ranked rank tree) :
    Ranked rank (source_remove_useless_node tree index).1 := by
  cases stored : tree.nodes.get index with
  | none => unfold_source_remove_useless_node;simpa only [stored,Id.run,pure] using ranked
  | some node =>
    unfold_source_remove_useless_node
    simp only [stored,Id.run,pure]
    intro query value present child member
    have different : query ≠ index := by
      intro same;subst query
      rw [GeneralBorrowFreshDeassignment.get_removed] at present
      cases present
    rw [GeneralBorrowSparseRemoval.remove_get_other tree.nodes index query different] at present
    exact ranked query value present child member

theorem reparent (rank : UniIndex → Nat) (tree : BorrowTree) (index parent : UniIndex)
    (node : TreeNode) (present : tree.nodes.get index = some node) (ranked : Ranked rank tree) :
    Ranked rank {tree with nodes := tree.nodes.insert index {node with parent := some parent}} := by
  intro query value found child member
  by_cases same : query = index
  · subst query
    rw [GeneralBorrowNodeUpdate.insert_existing_get_same tree.nodes index node _ present] at found
    cases found
    exact ranked index node present child member
  · rw [GeneralBorrowNodeUpdate.insert_existing_get_other tree.nodes index query node _ present same] at found
    exact ranked query value found child member

theorem finish (rank : UniIndex → Nat) (tree : BorrowTree) (index : UniIndex)
    (node : TreeNode) (present : tree.nodes.get index = some node) (kept : Array UniIndex)
    (children : ∀ child ∈ kept.toList, rank index < rank child) (ranked : Ranked rank tree) :
    Ranked rank {tree with nodes := tree.nodes.insert index {node with children := kept}} := by
  intro query value found child member
  by_cases same : query = index
  · subst query
    rw [GeneralBorrowNodeUpdate.insert_existing_get_same tree.nodes index node _ present] at found
    cases found
    exact children child member
  · rw [GeneralBorrowNodeUpdate.insert_existing_get_other tree.nodes index query node _ present same] at found
    exact ranked query value found child member
end DuplicatePrefix.GeneralBorrowGcStrictChildren
