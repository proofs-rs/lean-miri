import duplicate_prefix.GeneralRangeMapState
namespace DuplicatePrefix.GeneralRangeMapGeometry
open Miri Miri.ABI Miri.DataStructures
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem facts (map : DedupRangeMap α) (good : map.WellFormed) (nonempty : map.entries.size ≠ 0) :
    (map.entries[0]'(by omega)).range.start = 0 ∧
    (∀ index (valid : index < map.entries.size), map.entries[index].range.start.toNat < map.entries[index].range.stop.toNat) ∧
    (∀ index (valid : index+1 < map.entries.size), map.entries[index].range.stop.toNat = map.entries[index+1].range.start.toNat) := by
  simp only [DedupRangeMap.WellFormed,nonempty,↓reduceDIte] at good
  refine ⟨good.1,?_,?_⟩
  · intro index valid
    exact UInt64.lt_iff_toNat_lt.mp (good.2.1 index valid)
  · intro index valid
    exact congrArg UInt64.toNat (good.2.2 index valid)

theorem stop_le_start (map : DedupRangeMap α) (good : map.WellFormed)
    (first last : Nat) (ordered : first < last) (valid : last < map.entries.size) :
    (map.entries[first]'(by omega)).range.stop.toNat ≤ map.entries[last].range.start.toNat := by
  have state := facts map good (by omega)
  induction last with
  | zero => omega
  | succ last ih =>
    by_cases equal : first = last
    · subst first
      have adjacent := state.2.2 last valid
      omega
    · have before : first < last := by omega
      have oldValid : last < map.entries.size := by omega
      have earlier := ih before oldValid state
      have positive := state.2.1 last oldValid
      have adjacent := state.2.2 last valid
      omega

def Contains (map : DedupRangeMap α) (offset : UInt64) (index : Nat) : Prop :=
  ∃ valid : index < map.entries.size,
    map.entries[index].range.start.toNat ≤ offset.toNat ∧ offset.toNat < map.entries[index].range.stop.toNat

theorem contains_before (map : DedupRangeMap α) (good : map.WellFormed) (offset : UInt64)
    (last : Nat) (valid : last < map.entries.size)
    (inside : offset.toNat < map.entries[last].range.stop.toNat) :
    ∃ index, index ≤ last ∧ Contains map offset index := by
  have state := facts map good (by omega)
  induction last with
  | zero =>
    refine ⟨0,by omega,valid,?_,inside⟩
    rw [state.1]
    simp
  | succ last ih =>
    have oldValid : last < map.entries.size := by omega
    by_cases before : offset.toNat < map.entries[last].range.stop.toNat
    · obtain ⟨index,bounded,contains⟩ := ih oldValid before state
      exact ⟨index,by omega,contains⟩
    · refine ⟨last+1,by omega,valid,?_,inside⟩
      have adjacent := state.2.2 last valid
      omega

theorem size_last (map : DedupRangeMap α) (nonempty : 0 < map.entries.size) :
    map.size.bytes = (map.entries[map.entries.size-1]'(by omega)).range.stop := by
  unfold DedupRangeMap.size
  rw [Array.back?_eq_getElem?,Array.getElem?_eq_getElem (by omega)]
  rfl

theorem covered (map : DedupRangeMap α) (good : map.WellFormed) (offset : UInt64)
    (inside : offset.toNat < map.size.bytes.toNat) : ∃ index, Contains map offset index := by
  have nonempty : 0 < map.entries.size := by
    by_cases empty : map.entries.size = 0
    · have entries : map.entries = #[] := Array.size_eq_zero_iff.mp empty
      simp [DedupRangeMap.size,entries,Size.ZERO] at inside
    · omega
  rw [size_last map nonempty] at inside
  obtain ⟨index,_,contains⟩ := contains_before map good offset (map.entries.size-1) (by omega) inside
  exact ⟨index,contains⟩
end DuplicatePrefix.GeneralRangeMapGeometry
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralRangeMapGeometry." then
      for dependency in (←collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved general map geometry axiom {dependency}"
