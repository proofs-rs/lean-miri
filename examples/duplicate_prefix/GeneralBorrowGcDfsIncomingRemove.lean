import duplicate_prefix.GeneralBorrowGcDfsIncoming

namespace DuplicatePrefix.GeneralBorrowGcDfsIncomingRemove
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcDfsIncoming
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

theorem other (tree : BorrowTree) (index query : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) (different : query ≠ index) :
    (source_remove_useless_node tree index).1.nodes.get query = tree.nodes.get query := by
  unfold_source_remove_useless_node
  simp only [present,Id.run,pure]
  exact GeneralBorrowSparseRemoval.remove_get_other tree.nodes index query different

theorem self (tree : BorrowTree) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) : (source_remove_useless_node tree index).1.nodes.get index = none := by
  unfold_source_remove_useless_node
  simp only [present,Id.run,pure]
  exact GeneralBorrowFreshDeassignment.get_removed tree.nodes index

theorem inverse (tree : BorrowTree) (index query : UniIndex) (node value : TreeNode)
    (present : tree.nodes.get index = some node) (found : (source_remove_useless_node tree index).1.nodes.get query = some value) :
    query ≠ index ∧ tree.nodes.get query = some value := by
  have different : query ≠ index := by
    intro same;subst query
    rw [self tree index node present] at found
    cases found
  exact ⟨different,(other tree index query node present different).symm.trans found⟩

/-- Actual leaf deletion leaves no dangling incoming edge: completed incoming
backlinks show that a node with an empty repaired child array has no children. -/
theorem leaf (original tree : BorrowTree) (processed : List UniIndex) (parent index : UniIndex)
    (items : List UniIndex) (kept : Array UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) (empty : node.children = #[])
    (good : Active original processed parent (index::items) kept tree) :
    Active original processed parent items kept (source_remove_useless_node tree index).1 := by
  constructor
  · intro child value found otherParent edge completed
    obtain ⟨different,before⟩ := inverse tree index child node value present found
    obtain ⟨parentNode,parentPresent,member⟩ := good.completed child value before otherParent edge completed
    have parentDifferent : otherParent ≠ index := by
      intro same;subst otherParent
      have sameNode := Option.some.inj (present.symm.trans parentPresent)
      subst parentNode
      simp only [empty,Array.toList_empty,List.not_mem_nil] at member
    exact ⟨parentNode,(other tree index otherParent node present parentDifferent).trans parentPresent,member⟩
  · intro child value found otherParent edge outside
    obtain ⟨different,before⟩ := inverse tree index child node value present found
    exact good.unprocessed child value before otherParent edge outside
  · intro child value found
    obtain ⟨different,before⟩ := inverse tree index child node value present found
    exact good.origins child value before
  · intro child value found edge
    obtain ⟨different,before⟩ := inverse tree index child node value present found
    have covered := good.frontier child value before edge
    rcases List.mem_append.mp covered with keptMember | remaining
    · exact List.mem_append_left _ keptMember
    · exact List.mem_append_right _ ((List.mem_cons.mp remaining).resolve_left different)

end DuplicatePrefix.GeneralBorrowGcDfsIncomingRemove
