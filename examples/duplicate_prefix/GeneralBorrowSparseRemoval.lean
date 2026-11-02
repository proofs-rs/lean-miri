import duplicate_prefix.GeneralBorrowFreshDeassignment
namespace DuplicatePrefix.GeneralBorrowSparseRemoval
open Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxHeartbeats 300000

/-- Actual sparse removal retains allocated table capacity, including a missing
index. No compacting or allocator behavior is substituted for the source. -/
theorem remove_size {α : Type} (map : UniValMap α) (index : UniIndex) :
    (map.remove index).size = map.size := by
  unfold UniValMap.remove
  split <;> simp only [UniValMap.size,Array.size_set]

/-- Every nonremoved optional slot is preserved, independently of its presence
or whether the removed index is within the table. -/
theorem remove_get_other {α : Type} (map : UniValMap α) (index query : UniIndex) (different : query ≠ index) :
    (map.remove index).get query = map.get query := by
  have differentNat : query.toNat ≠ index.toNat := fun same => different (GeneralBorrowNodeUpdate.index_injective query index same)
  unfold UniValMap.remove
  split
  · unfold UniValMap.get
    simp only [Array.getElem?_set,differentNat,Ne.symm differentNat,↓reduceIte]
  · rfl
end DuplicatePrefix.GeneralBorrowSparseRemoval
