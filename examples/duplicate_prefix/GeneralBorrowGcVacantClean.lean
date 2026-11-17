import duplicate_prefix.GeneralBorrowFreshDeassignment
import duplicate_prefix.GeneralBorrowFreshFutureClean
import duplicate_prefix.GeneralBorrowSparseRemoval
namespace DuplicatePrefix.GeneralBorrowGcVacantClean
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralBorrowFreshFutureClean
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

open Lean Elab Term in
elab "gc_source_root_index" : term => do
  let found := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".BorrowTree.rootIndex" then some name else none
  match found with
  | [name] => return mkConst name
  | _ => throwError "expected pinned tree root index"
private theorem root_zero : gc_source_root_index = (⟨0⟩ : UniIndex) := rfl

/-- Vacant node slots carry no stored permissions anywhere in the allocation.
This is stronger than node vacancy, and imposes no permission condition on live nodes. -/
def VacantClean (tree : BorrowTree) : Prop :=
  ∀ query, tree.nodes.get query = none → Clean tree query

/-- The actual allocation constructor establishes the vacant-slot invariant. -/
theorem initial (tag : BorTag) (size : Size) : VacantClean (BorrowTree.new tag size) := by
  intro query vacant position valid
  have different : query ≠ (⟨0⟩ : UniIndex) := by
    intro equal
    subst query
    simp [BorrowTree.new,UniValMap.insert,UniValMap.get,UniValMap.extendTo,root_zero,UniIndex.toNat] at vacant
  have positive : 0 < query.toNat := by
    have ne : query.toNat ≠ 0 := by
      intro equal
      apply different
      exact GeneralBorrowNodeUpdate.index_injective query ⟨0⟩ equal
    omega
  by_cases zero : size.bytes = 0
  · have impossible : position < 0 := by
      simpa [BorrowTree.new,DedupRangeMap.new,zero,root_zero,Id.run,bind,pure] using valid
    omega
  · have bounded : position < 1 := by
      simpa [BorrowTree.new,DedupRangeMap.new,zero,root_zero,Id.run,bind,pure] using valid
    have atZero : position = 0 := by omega
    subst position
    simp [BorrowTree.new,DedupRangeMap.new,UniValMap.insert,UniValMap.get,UniValMap.extendTo,
      root_zero,UniIndex.toNat,zero]
    cases converted : query.idx.toNat with
    | zero => have impossible : query.toNat = 0 := converted;omega
    | succ next => simp [converted]
/-- GC's parent/child metadata rewrites use this actual sparse insertion.
Inserting a node creates no new vacancy, so no location permission assumption
for that live index is needed. -/
theorem insert_preserves (tree : BorrowTree) (index : UniIndex) (node : TreeNode) (good : VacantClean tree) :
    VacantClean {tree with nodes := tree.nodes.insert index node} := by
  intro query vacant
  change (tree.nodes.insert index node).get query = none at vacant
  by_cases equal : query = index
  · subst query
    rw [GeneralBorrowFreshLocation.get_same] at vacant
    cases vacant
  · rw [GeneralBorrowFreshLocation.get_other _ index query node equal] at vacant
    exact good query vacant

/-- The production GC removal primitive preserves every existing vacant slot
and creates a clean vacancy at the removed index. Missing-node errors leave
the input unchanged. GC eligibility and tag/index consistency are separate. -/
theorem remove_preserves (tree : BorrowTree) (index : UniIndex) (good : VacantClean tree) :
    VacantClean (source_remove_useless_node tree index).1 := by
  cases stored : tree.nodes.get index with
  | none =>
    unfold_source_remove_useless_node
    simpa only [stored,Id.run,bind,pure] using good
  | some node =>
    unfold_source_remove_useless_node
    simp only [stored,Id.run,bind,pure]
    intro query vacant position valid
    change (tree.nodes.remove index).get query = none at vacant
    have previous : position < tree.locations.entries.size := by
      simpa only [DedupRangeMap.modifyAll,Array.size_map] using valid
    have cleared : ((tree.locations.entries[position]'previous).data.perms.remove index).get query = none := by
      by_cases equal : query = index
      · subst query
        exact GeneralBorrowFreshDeassignment.get_removed _ index
      · rw [GeneralBorrowSparseRemoval.remove_get_other _ index query equal]
        rw [GeneralBorrowSparseRemoval.remove_get_other _ index query equal] at vacant
        exact good query vacant position previous
    simpa only [DedupRangeMap.modifyAll,Array.getElem_map] using cleared

end DuplicatePrefix.GeneralBorrowGcVacantClean
