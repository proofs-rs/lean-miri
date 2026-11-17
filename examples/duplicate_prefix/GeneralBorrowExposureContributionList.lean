import duplicate_prefix.GeneralBorrowExposurePointwise
namespace DuplicatePrefix.GeneralBorrowExposureContributionList
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposureAncestorFold
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Replacing one distinct finite source changes only its own Boolean witness. -/
theorem balance {α : Type} [DecidableEq α] (rows : List α) (unique : rows.Nodup)
    (source : α) (member : source ∈ rows) (old new : α → Bool)
    (unchanged : ∀ row ∈ rows,row ≠ source → old row = new row) :
    (rows.filter new).length + (if old source then 1 else 0) =
      (rows.filter old).length + (if new source then 1 else 0) := by
  induction rows with
  | nil => cases member
  | cons row rest ih =>
    have distinct := List.nodup_cons.mp unique
    by_cases same : row = source
    · subst row
      have tailEq : rest.filter old = rest.filter new := List.filter_congr (by
        intro row member
        apply unchanged row (by simp [member])
        intro same;subst row;exact distinct.1 member)
      cases oldValue : old source <;> cases newValue : new source
      all_goals simp only [List.filter_cons,oldValue,newValue,Bool.false_eq_true,ite_false,ite_true,List.length_cons,tailEq]
      all_goals omega
    · have sourceLater : source ∈ rest := by rcases List.mem_cons.mp member with equal | tail;exact False.elim (same equal.symm);exact tail
      have continued := ih distinct.2 sourceLater (fun other member => unchanged other (by simp [member]))
      have equal := unchanged row (by simp) same
      cases value : old row
      all_goals have newValue : new row = _ := equal.symm.trans value
      all_goals simp only [List.filter_cons,value,newValue,Bool.false_eq_true,ite_false,ite_true,List.length_cons]
      all_goals omega

/-- The balance law interprets the actual finite-width increment/decrement,
including wrap, without a Nat-counter-budget premise. -/
theorem modular_delta (oldCount newCount : Nat) (before after : Bool)
    (balance : newCount+(if before then 1 else 0) = oldCount+(if after then 1 else 0)) :
    UInt16.ofNat newCount = delta (UInt16.ofNat oldCount) before after := by
  cases before <;> cases after
  · simp only [Bool.false_eq_true,ite_false,Nat.add_zero] at balance
    rw [balance];rfl
  · have same : newCount = oldCount+1 := by simpa using balance
    rw [same,UInt16.ofNat_add];rfl
  · have same : oldCount = newCount+1 := by simpa using balance.symm
    rw [same,UInt16.ofNat_add]
    exact (UInt16.add_sub_cancel _ _).symm
  · have same : oldCount = newCount := by simpa using balance.symm
    rw [same];rfl

private theorem slot_index {α : Type} (data : Array (Option α)) (position : Nat) (row : UniIndex × α)
    (found : GeneralBorrowFreshEntries.slot data position = some row) : row.1.toNat = position := by
  unfold GeneralBorrowFreshEntries.slot at found
  cases converted : UniIndex.ofNat? position with
  | none => simp [converted] at found
  | some index =>
    cases stored : data[position]? with
    | none => simp [converted,stored] at found
    | some cell =>
      cases cell with
      | none => simp [converted,stored] at found
      | some node =>
        simp only [converted,stored,Option.some.injEq] at found
        subst row
        unfold UniIndex.ofNat? at converted
        split at converted
        next bounded => cases converted;simp only [UniIndex.toNat,UInt32.toNat_ofNat'];omega
        next => contradiction

/-- The real optional-slot enumeration has distinct source indices, derived
from its actual filtering loop rather than assumed as cache metadata. -/
theorem entries_keys {α : Type} (nodes : UniValMap α) :
    nodes.entries.toList.Pairwise (fun left right => left.1 ≠ right.1) := by
  rw [GeneralBorrowFreshEntries.entries_formula]
  refine List.Pairwise.filterMap (GeneralBorrowFreshEntries.slot nodes.data) ?_ List.nodup_range'
  intro left right different row found other otherFound same
  have before := slot_index nodes.data left row found
  have after := slot_index nodes.data right other otherFound
  apply different
  exact before.symm.trans ((congrArg UniIndex.toNat same).trans after)

theorem entries_nodup {α : Type} (nodes : UniValMap α) : nodes.entries.toList.Nodup :=
  (entries_keys nodes).imp (fun different same => different (congrArg Prod.fst same))
end DuplicatePrefix.GeneralBorrowExposureContributionList
