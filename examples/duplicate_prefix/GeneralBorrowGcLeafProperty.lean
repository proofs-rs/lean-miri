import duplicate_prefix.GeneralBorrowGcLeafFold

namespace DuplicatePrefix.GeneralBorrowGcLeafProperty
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcWalker DuplicatePrefix.GeneralBorrowGcChildFold
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

open DuplicatePrefix.GeneralBorrowGcLeafFold (step)

private theorem removal_other (tree : BorrowTree) (index query : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) (different : query ≠ index) :
    (source_remove_useless_node tree index).1.nodes.get query = tree.nodes.get query := by
  unfold_source_remove_useless_node
  simp only [present,Id.run,bind,pure]
  exact GeneralBorrowSparseRemoval.remove_get_other tree.nodes index query different

private theorem removal_capacity (tree : BorrowTree) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) :
    (source_remove_useless_node tree index).1.nodes.size = tree.nodes.size := by
  unfold_source_remove_useless_node
  simp only [present,Id.run,bind,pure]
  exact GeneralBorrowSparseRemoval.remove_size tree.nodes index

/-- Distinct, present childless nodes suffice for the real GC child fold to
complete. Deletion never invalidates a later item, and all outside lookups and
sparse capacity are preserved. No operation success is assumed. -/
theorem complete (P : BorrowTree → Prop)
    (removed : ∀ tree index, P tree → P (source_remove_useless_node tree index).1)
    (items : List UniIndex) (seed tree : BorrowTree) (root parent : UniIndex)
    (live : Array BorTag) (kept : Array UniIndex) (distinct : items.Nodup)
    (leaves : ∀ index ∈ items, ∃ node, tree.nodes.get index = some node ∧ node.children = #[]) (initial : P tree) :
    ∃ after result, forIn items (none,tree,kept) (childScan seed root live parent) = (none,after,result) ∧
      after.nodes.size = tree.nodes.size ∧
      (∀ query, query ∉ items → after.nodes.get query = tree.nodes.get query) ∧ P after := by
  induction items generalizing tree kept with
  | nil => exact ⟨tree,kept,rfl,rfl,fun _ _ => rfl,initial⟩
  | cons index rest ih =>
    obtain ⟨node,present,empty⟩ := leaves index (by simp)
    have tailDistinct := (List.nodup_cons.mp distinct).2
    rw [List.forIn_cons,step seed tree root parent index live node present empty kept]
    cases held : live.contains node.tag with
    | true =>
      simp only [held,↓reduceIte,bind]
      obtain ⟨after,result,done,size,outside,afterGood⟩ := ih tree (kept.push index) tailDistinct
        (fun query member => leaves query (by simp [member])) initial
      exact ⟨after,result,done,size,fun query absent => outside query (fun member => absent (by simp [member])),afterGood⟩
    | false =>
      simp only [held,↓reduceIte,bind]
      have nextLeaves : ∀ query ∈ rest, ∃ value,
          (source_remove_useless_node tree index).1.nodes.get query = some value ∧ value.children = #[] := by
        intro query member
        obtain ⟨value,lookup,empty⟩ := leaves query (by simp [member])
        have different : query ≠ index := fun same => (List.nodup_cons.mp distinct).1 (same ▸ member)
        exact ⟨value,(removal_other tree index query node present different).trans lookup,empty⟩
      obtain ⟨after,result,done,size,outside,afterGood⟩ := ih (source_remove_useless_node tree index).1 kept tailDistinct nextLeaves (removed tree index initial)
      refine ⟨after,result,done,size.trans (removal_capacity tree index node present),?_,afterGood⟩
      intro query absent
      have different : query ≠ index := fun same => absent (by simp [same])
      exact (outside query (fun member => absent (by simp [member]))).trans
        (removal_other tree index query node present different)

end DuplicatePrefix.GeneralBorrowGcLeafProperty
