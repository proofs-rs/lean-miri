import duplicate_prefix.GeneralBorrowFreshInstallation

namespace DuplicatePrefix.S02DisjointConstructorMap
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- The real range modifier preserves every row predicate on a disjoint byte
window. This concerns the physical location map before constructor topology
and allocation-wide SIFA are updated. -/
theorem modify_outside {α : Type} [DecidableEq α] (map : DedupRangeMap α)
    (offset len : Size) (modify : ByteRange → α → α)
    (idempotent : ∀ range value, modify range (modify range value) = modify range value)
    (predicate : α → Prop) (lower upper : UInt64)
    (well : map.WellFormed)
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ map.size.bytes.toNat)
    (outside : offset.bytes.toNat + len.bytes.toNat ≤ lower.toNat ∨
      upper.toNat ≤ offset.bytes.toNat)
    (owned : OwnedOn predicate lower upper map) :
    OwnedOn predicate lower upper (map.modifyRange offset len modify).state := by
  let prepared := map.iterMut offset len
  let changed := map.modifyRange offset len modify
  have preparedData := GeneralRangeMapOriginPrepare.iter_mut map offset len well bounds
  have preparedOwned := refines_owned_on map prepared.state predicate lower upper
    preparedData.1.wellFormed preparedData.2.1 owned
  have sizes : changed.state.entries.size = prepared.state.entries.size := by
    dsimp only [changed,prepared]
    rw [GeneralBorrowFreshModify.state_exact map offset len modify well bounds,
      GeneralBorrowFreshModify.fold_size]
  intro query valid positive beforeUpper afterLower
  have preparedValid : query < prepared.state.entries.size := by
    rw [←sizes]
    exact valid
  obtain ⟨outputValid,entryEq⟩ := GeneralBorrowFreshModify.entry_exact map offset len
    modify idempotent well bounds query preparedValid
  have validEq : outputValid = valid := Subsingleton.elim _ _
  subst outputValid
  have notSelected : query ∉ prepared.positions.toList := by
    intro member
    obtain ⟨cursor,cursorValid,selectedEq⟩ := Array.mem_iff_getElem.mp
      (Array.mem_def.mpr member)
    have good := preparedData.1
    have segmentValid : cursor < prepared.segments.size := by
      rw [←good.lengths]
      exact cursorValid
    obtain ⟨positionValid,segmentEq⟩ := good.selected cursor cursorValid
    have queryEq : prepared.positions[cursor] = query := selectedEq
    have queryEq' : (map.iterMut offset len).positions[cursor] = query := queryEq
    have selectedRow : prepared.segments[cursor] = prepared.state.entries[query] := by
      simpa only [queryEq'] using segmentEq
    have selectedWithin := preparedData.2.2 cursor segmentValid
    rw [selectedRow] at selectedWithin
    have fits : offset.bytes.toNat + len.bytes.toNat < 2^64 :=
      Nat.lt_of_le_of_lt bounds map.size.bytes.toNat_lt
    have stopEq : (offset.bytes+len.bytes).toNat = offset.bytes.toNat+len.bytes.toNat := by
      rw [UInt64.toNat_add,Nat.mod_eq_of_lt fits]
    rw [stopEq] at selectedWithin
    have sameRange : changed.state.entries[query].range = prepared.state.entries[query].range := by
      rw [entryEq]
      split <;> rfl
    rw [sameRange] at beforeUpper afterLower
    rcases outside with left | right <;> omega
  change query ∉ (map.iterMut offset len).positions.toList at notSelected
  simp [notSelected] at entryEq
  rw [entryEq] at beforeUpper afterLower ⊢
  exact preparedOwned query preparedValid positive beforeUpper afterLower

/-- Specialization to the actual protected mutable child materialization. -/
theorem mutable_materialized (map : DedupRangeMap LocationTree)
    (offset len : Size) (index : UniIndex) (predicate : LocationTree → Prop)
    (lower upper : UInt64) (well : map.WellFormed)
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ map.size.bytes.toNat)
    (outside : offset.bytes.toNat + len.bytes.toNat ≤ lower.toNat ∨
      upper.toNat ≤ offset.bytes.toNat)
    (owned : OwnedOn predicate lower upper map) :
    OwnedOn predicate lower upper
      (map.modifyRange offset len (fun _ location =>
        GeneralBorrowFreshMaterialization.materialized location index GeneralBorrowFreshChild.inside)).state := by
  exact modify_outside map offset len _
    (fun _ location => GeneralBorrowFreshInstallation.materialized_idempotent location index GeneralBorrowFreshChild.inside)
    predicate lower upper well bounds outside owned

end DuplicatePrefix.S02DisjointConstructorMap

open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S02DisjointConstructorMap.modify_outside,
      ``DuplicatePrefix.S02DisjointConstructorMap.mutable_materialized] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
