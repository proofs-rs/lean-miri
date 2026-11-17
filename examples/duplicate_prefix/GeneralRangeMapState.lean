import duplicate_prefix.RangeMapNonempty
namespace DuplicatePrefix.GeneralRangeMapState
open Miri Miri.ABI Miri.DataStructures
open Lean Elab Tactic
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
elab "unfold_range_update_source" : tactic => do
  let names := (← getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".DedupRangeMap.segmentAt?" || name.toString.endsWith ".DedupRangeMap.updateAt" then some (mkIdent name) else none
  let names := names.toArray
  evalTactic (← `(tactic| simp only [$[$names:ident],*]))

def replaced (map : DedupRangeMap α) (position : Nat) (valid : position < map.entries.size) (data : α) : DedupRangeMap α :=
  ⟨map.entries.set position {map.entries[position] with data := data} valid⟩

theorem setAtPos_exact (map : DedupRangeMap α) (position : Nat) (valid : position < map.entries.size) (data : α) :
    map.setAtPos position data = ⟨replaced map position valid data,.ok ()⟩ := by
  unfold DedupRangeMap.setAtPos
  unfold_range_update_source
  simp [valid,replaced,Except.pure,pure,Id.run]

theorem index_exact (map : DedupRangeMap α) (position : Nat) (valid : position < map.entries.size) :
    map.index position = .ok map.entries[position] := by
  unfold DedupRangeMap.index
  unfold_range_update_source
  simp [valid,Except.pure,pure]

theorem setAtPos_success (map : DedupRangeMap α) (position : Nat) (valid : position < map.entries.size) (data : α) :
    (map.setAtPos position data).outcome = .ok () := by
  rw [setAtPos_exact map position valid data]

theorem setAtPos_length (map : DedupRangeMap α) (position : Nat) (valid : position < map.entries.size) (data : α) :
    (map.setAtPos position data).state.entries.size = map.entries.size := by
  rw [setAtPos_exact map position valid data]
  simp only [replaced,Array.size_set]

theorem replaced_length (map : DedupRangeMap α) (position : Nat) (valid : position < map.entries.size) (data : α) :
    (replaced map position valid data).entries.size = map.entries.size := by
  simp only [replaced,Array.size_set]

theorem replaced_range (map : DedupRangeMap α) (position : Nat) (valid : position < map.entries.size) (data : α)
    (index : Nat) (bounded : index < map.entries.size) :
    ((replaced map position valid data).entries[index]'(by simpa only [replaced_length] using bounded)).range = map.entries[index].range := by
  by_cases equal : position = index
  · subst index
    simp [replaced]
  · simp [replaced,Array.getElem_set,equal]

theorem replaced_ranges (map : DedupRangeMap α) (position : Nat) (valid : position < map.entries.size) (data : α) :
    (replaced map position valid data).entries.map (·.range) = map.entries.map (·.range) := by
  apply Array.ext
  · simp [replaced]
  · intro index left right
    simp only [Array.getElem_map]
    exact replaced_range map position valid data index (by simpa only [Array.size_map] using right)

theorem size_from_ranges (map : DedupRangeMap α) :
    map.size = match (map.entries.map (·.range)).back? with
      | none => Size.ZERO
      | some range => Size.ofBytes range.stop := by
  rw [Array.back?_map]
  unfold DedupRangeMap.size
  cases map.entries.back? <;> rfl

theorem replaced_size (map : DedupRangeMap α) (position : Nat) (valid : position < map.entries.size) (data : α) :
    (replaced map position valid data).size = map.size := by
  rw [size_from_ranges,replaced_ranges,←size_from_ranges]

theorem replaced_wellFormed (map : DedupRangeMap α) (position : Nat) (valid : position < map.entries.size) (data : α)
    (good : map.WellFormed) : (replaced map position valid data).WellFormed := by
  have nonempty : map.entries.size ≠ 0 := by omega
  simp only [DedupRangeMap.WellFormed,nonempty,↓reduceDIte] at good
  simp only [DedupRangeMap.WellFormed,replaced_length,nonempty,↓reduceDIte]
  refine ⟨?_,?_,?_⟩
  · rw [replaced_range map position valid data 0 (by omega)]
    exact good.1
  · intro index bounded
    rw [replaced_range map position valid data index bounded]
    exact good.2.1 index bounded
  · intro index bounded
    rw [replaced_range map position valid data index (by omega),replaced_range map position valid data (index+1) bounded]
    exact good.2.2 index bounded

def Every (predicate : α → Prop) (map : DedupRangeMap α) : Prop :=
  ∀ index (valid : index < map.entries.size), predicate map.entries[index].data

theorem replaced_every (predicate : α → Prop) (map : DedupRangeMap α)
    (position : Nat) (valid : position < map.entries.size) (data : α)
    (all : Every predicate map) (newGood : predicate data) : Every predicate (replaced map position valid data) := by
  intro index bounded
  have oldBound : index < map.entries.size := by simpa only [replaced_length] using bounded
  by_cases equal : position = index
  · subst index
    simpa [replaced] using newGood
  · simpa [replaced,Array.getElem_set,equal] using all index oldBound

end DuplicatePrefix.GeneralRangeMapState
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralRangeMapState." then
      for dependency in (←collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved general map state axiom {dependency}"
