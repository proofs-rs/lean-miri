import duplicate_prefix.GeneralBorrowFreshNode
namespace DuplicatePrefix.GeneralBorrowFreshLocation
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowNodeUpdate
set_option maxRecDepth 65536
set_option maxHeartbeats 100000

/-- Extending a sparse location map with absent entries preserves every lookup,
including queries beyond both its old and new extents. -/
theorem extend_get {α : Type} (map : UniValMap α) (length : Nat) (index : UniIndex) :
    (⟨UniValMap.extendTo map.data length⟩ : UniValMap α).get index = map.get index := by
  unfold UniValMap.get UniValMap.extendTo
  rw [Array.getElem?_append]
  by_cases valid : index.toNat < map.data.size
  · simp only [valid,↓reduceIte]
  · have absent : map.data[index.toNat]? = none := Array.getElem?_eq_none (by omega)
    simp only [valid,↓reduceIte,absent,Array.getElem?_replicate]
    by_cases inside : index.toNat-map.data.size < length-map.data.size <;> simp only [inside,↓reduceIte]

private theorem extended_bound {α : Type} (map : UniValMap α) (index : UniIndex) :
    index.toNat < (UniValMap.extendTo map.data (index.toNat+1)).size := by
  simp only [UniValMap.extendTo,Array.size_append,Array.size_replicate]
  omega

private theorem inserted_data {α : Type} (map : UniValMap α) (index : UniIndex) (value : α) :
    (map.insert index value).data =
      (UniValMap.extendTo map.data (index.toNat+1)).set index.toNat (some value) (extended_bound map index) := by
  simp only [UniValMap.insert,extended_bound map index,↓reduceDIte,Id.run,pure]

/-- The actual sparse-map insertion stores the new child's materialized state. -/
theorem get_same {α : Type} (map : UniValMap α) (index : UniIndex) (value : α) :
    (map.insert index value).get index = some value := by
  unfold UniValMap.get
  rw [inserted_data]
  simp

/-- Inserting the new child state preserves every other node's state even
when the per-location sparse array has a different length from the node table. -/
theorem get_other {α : Type} (map : UniValMap α) (index query : UniIndex) (value : α) (different : query ≠ index) :
    (map.insert index value).get query = map.get query := by
  have differentNat : query.toNat ≠ index.toNat := fun equal => different (index_injective query index equal)
  unfold UniValMap.get
  rw [inserted_data]
  simp only [Array.getElem?_set,Ne.symm differentNat,↓reduceIte]
  exact extend_get map (index.toNat+1) query

/-- The actual materialization record update leaves the exposed cache intact. -/
theorem materialize_cache (location : LocationTree) (index : UniIndex) (state : LocationState) :
    ({location with perms := location.perms.insert index state} : LocationTree).exposedCache = location.exposedCache := rfl

end DuplicatePrefix.GeneralBorrowFreshLocation
#print axioms DuplicatePrefix.GeneralBorrowFreshLocation.get_other
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshLocation." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved materialization dependency {dependency}"
