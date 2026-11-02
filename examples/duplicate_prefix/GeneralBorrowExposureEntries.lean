import duplicate_prefix.GeneralBorrowExposureLevelUpdate
namespace DuplicatePrefix.GeneralBorrowExposureEntries
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowNodeUpdate
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private theorem converted_nat (position : Nat) (index : UniIndex) (converted : UniIndex.ofNat? position = some index) : index.toNat = position := by
  unfold UniIndex.ofNat? at converted
  split at converted
  next bounded => cases converted;simp only [UniIndex.toNat,UInt32.toNat_ofNat'];omega
  next => contradiction

theorem slot_get {α : Type} (nodes : UniValMap α) (position : Nat) :
    GeneralBorrowFreshEntries.slot nodes.data position =
      (UniIndex.ofNat? position).bind (fun index => (nodes.get index).map (fun value => (index,value))) := by
  cases converted : UniIndex.ofNat? position with
  | none => simp only [GeneralBorrowFreshEntries.slot,converted,Option.bind_none]
  | some index =>
    have same := converted_nat position index converted
    simp only [GeneralBorrowFreshEntries.slot,converted,Option.bind_some,UniValMap.get,same]
    cases stored : nodes.data[position]? with
    | none => rfl
    | some cell => cases cell <;> rfl

def replaceRow {α : Type} (index : UniIndex) (value : α) (row : UniIndex × α) : UniIndex × α :=
  if row.1 = index then (index,value) else row

/-- Updating a present source changes exactly its actual enumeration row. -/
theorem insert {α : Type} (nodes : UniValMap α) (index : UniIndex) (old value : α)
    (present : nodes.get index = some old) :
    (nodes.insert index value).entries.toList = nodes.entries.toList.map (replaceRow index value) := by
  rw [GeneralBorrowFreshEntries.entries_formula,GeneralBorrowFreshEntries.entries_formula]
  have size : (nodes.insert index value).data.size = nodes.data.size := insert_existing_size nodes index old value present
  rw [size]
  simp only [List.map_filterMap]
  have slots : GeneralBorrowFreshEntries.slot (nodes.insert index value).data =
      fun position => (GeneralBorrowFreshEntries.slot nodes.data position).map (replaceRow index value) := by
    funext position
    rw [slot_get,slot_get]
    cases converted : UniIndex.ofNat? position with
    | none => rfl
    | some query =>
      simp only [Option.bind_some]
      by_cases same : query = index
      · subst query
        rw [insert_existing_get_same nodes index old value present,present]
        simp only [Option.map_some,replaceRow,ite_true]
      · rw [insert_existing_get_other nodes index query old value present same]
        cases found : nodes.get query with
        | none => rfl
        | some oldNode => simp only [Option.map_some,replaceRow,ite_eq_right same]
  rw [slots]
end DuplicatePrefix.GeneralBorrowExposureEntries
