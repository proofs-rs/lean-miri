import duplicate_prefix.GeneralRangeMapGeometry
namespace DuplicatePrefix.GeneralRangeMapSplit
open Miri Miri.ABI Miri.DataStructures
open DuplicatePrefix.RangeMapNonempty GeneralRangeMapState GeneralRangeMapGeometry
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def splitMap (map : DedupRangeMap α) (position : Nat) (valid : position < map.entries.size)
    (offset : UInt64) (cloneData : α → α) : DedupRangeMap α :=
  let first := {map.entries[position] with range := {map.entries[position].range with stop := offset}}
  let second := {map.entries[position] with range := {map.entries[position].range with start := offset}, data := cloneData map.entries[position].data}
  let entries := map.entries.set position first valid
  ⟨entries.insertIdx (position+1) second (by simp only [entries,Array.size_set];omega)⟩

theorem length (map : DedupRangeMap α) (position : Nat) (valid : position < map.entries.size)
    (offset : UInt64) (cloneData : α → α) :
    (splitMap map position valid offset cloneData).entries.size = map.entries.size+1 := by
  simp only [splitMap,Array.size_insertIdx,Array.size_set]

theorem actual_inside (map : DedupRangeMap α) (position : Nat) (valid : position < map.entries.size)
    (offset : UInt64) (cloneData : α → α)
    (afterStart : map.entries[position].range.start < offset) (beforeEnd : offset < map.entries[position].range.stop) :
    range_split_index map.entries position offset cloneData = .ok ((splitMap map position valid offset cloneData).entries,true) := by
  have startNe : offset ≠ map.entries[position].range.start := by
    simp only [UInt64.lt_iff_toNat_lt] at afterStart
    intro equal
    rw [equal] at afterStart
    omega
  have stopNe : offset ≠ map.entries[position].range.stop := by
    simp only [UInt64.lt_iff_toNat_lt] at beforeEnd
    intro equal
    rw [equal] at beforeEnd
    omega
  have notBefore : ¬ offset < map.entries[position].range.start := by
    simp only [UInt64.lt_iff_toNat_lt] at *
    omega
  have notAfter : ¬ offset ≥ map.entries[position].range.stop := by
    simp only [ge_iff_le,UInt64.le_iff_toNat_le,UInt64.lt_iff_toNat_lt] at *
    omega
  simp_range_helpers
  simp [valid,startNe,stopNe,notBefore,notAfter,splitMap ]

theorem start_left (map : DedupRangeMap α) (position : Nat) (valid : position < map.entries.size)
    (offset : UInt64) (cloneData : α → α) (index : Nat) (before : index ≤ position) :
    ((splitMap map position valid offset cloneData).entries[index]'(by rw [length];omega)).range.start =
      (map.entries[index]'(by omega)).range.start := by
  dsimp only [splitMap]
  rw [Array.getElem_insertIdx_of_lt _ (by omega)]
  by_cases equal : position = index
  · subst index
    simp
  · simp [Array.getElem_set,equal]

theorem stop_left (map : DedupRangeMap α) (position : Nat) (valid : position < map.entries.size)
    (offset : UInt64) (cloneData : α → α) (index : Nat) (before : index < position) :
    ((splitMap map position valid offset cloneData).entries[index]'(by rw [length];omega)).range.stop =
      (map.entries[index]'(by omega)).range.stop := by
  dsimp only [splitMap]
  rw [Array.getElem_insertIdx_of_lt _ (by omega)]
  simp [Array.getElem_set,show position ≠ index by omega]

theorem stop_first (map : DedupRangeMap α) (position : Nat) (valid : position < map.entries.size)
    (offset : UInt64) (cloneData : α → α) :
    ((splitMap map position valid offset cloneData).entries[position]'(by rw [length];omega)).range.stop = offset := by
  dsimp only [splitMap]
  rw [Array.getElem_insertIdx_of_lt _ (by omega),Array.getElem_set_self]

theorem start_second (map : DedupRangeMap α) (position : Nat) (valid : position < map.entries.size)
    (offset : UInt64) (cloneData : α → α) :
    ((splitMap map position valid offset cloneData).entries[position+1]'(by rw [length];omega)).range.start = offset := by
  dsimp only [splitMap]
  simp only [Array.getElem_insertIdx_self]

theorem stop_right (map : DedupRangeMap α) (position : Nat) (valid : position < map.entries.size)
    (offset : UInt64) (cloneData : α → α) (index : Nat)
    (after : position < index) (bounded : index ≤ map.entries.size) :
    ((splitMap map position valid offset cloneData).entries[index]'(by rw [length];omega)).range.stop =
      (map.entries[index-1]'(by omega)).range.stop := by
  by_cases equal : index = position+1
  · subst index
    dsimp only [splitMap]
    simp only [Array.getElem_insertIdx_self,Nat.add_sub_cancel]
  · dsimp only [splitMap]
    rw [Array.getElem_insertIdx_of_gt (by simpa only [Array.size_set] using bounded) (by omega)]
    simp [Array.getElem_set,show position ≠ index-1 by omega]

theorem start_right (map : DedupRangeMap α) (position : Nat) (valid : position < map.entries.size)
    (offset : UInt64) (cloneData : α → α) (index : Nat)
    (after : position+1 < index) (bounded : index ≤ map.entries.size) :
    ((splitMap map position valid offset cloneData).entries[index]'(by rw [length];omega)).range.start =
      (map.entries[index-1]'(by omega)).range.start := by
  dsimp only [splitMap]
  rw [Array.getElem_insertIdx_of_gt (by simpa only [Array.size_set] using bounded) after]
  simp [Array.getElem_set,show position ≠ index-1 by omega]

theorem wellFormed (map : DedupRangeMap α) (position : Nat) (valid : position < map.entries.size)
    (offset : UInt64) (cloneData : α → α) (good : map.WellFormed)
    (afterStart : map.entries[position].range.start < offset) (beforeEnd : offset < map.entries[position].range.stop) :
    (splitMap map position valid offset cloneData).WellFormed := by
  have oldNonempty : map.entries.size ≠ 0 := by omega
  have state : map.entries[0].range.start = 0 ∧
      (∀ index (valid : index < map.entries.size), map.entries[index].range.start < map.entries[index].range.stop) ∧
      (∀ index (valid : index+1 < map.entries.size), map.entries[index].range.stop = map.entries[index+1].range.start) := by
    simpa only [DedupRangeMap.WellFormed,oldNonempty,↓reduceDIte] using good
  simp only [DedupRangeMap.WellFormed,length,Nat.add_one_ne_zero,↓reduceDIte]
  refine ⟨?_,?_,?_⟩
  · rw [start_left map position valid offset cloneData 0 (by omega)]
    exact state.1
  · intro index bounded
    by_cases before : index < position
    · rw [start_left map position valid offset cloneData index (by omega),stop_left map position valid offset cloneData index before]
      exact state.2.1 index (by omega)
    · by_cases same : index = position
      · subst index
        rw [start_left map position valid offset cloneData position (by omega),stop_first]
        exact afterStart
      · by_cases second : index = position+1
        · subst index
          rw [start_second,stop_right map position valid offset cloneData (position+1) (by omega) (by omega)]
          simpa only [Nat.add_sub_cancel] using beforeEnd
        · rw [start_right map position valid offset cloneData index (by omega) (by omega),stop_right map position valid offset cloneData index (by omega) (by omega)]
          exact state.2.1 (index-1) (by omega)
  · intro index bounded
    by_cases before : index < position
    · rw [stop_left map position valid offset cloneData index before,start_left map position valid offset cloneData (index+1) (by omega)]
      exact state.2.2 index (by omega)
    · by_cases same : index = position
      · subst index
        rw [stop_first,start_second]
      · rw [stop_right map position valid offset cloneData index (by omega) (by omega),start_right map position valid offset cloneData (index+1) (by omega) (by omega)]
        have adjacent := state.2.2 (index-1) (by omega)
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ index),Nat.add_sub_cancel] using adjacent

theorem size_bytes (map : DedupRangeMap α) (position : Nat) (valid : position < map.entries.size)
    (offset : UInt64) (cloneData : α → α) :
    (splitMap map position valid offset cloneData).size.bytes = map.size.bytes := by
  have last := size_last (splitMap map position valid offset cloneData) (by rw [length];omega)
  have lastEq : (splitMap map position valid offset cloneData).size.bytes =
      ((splitMap map position valid offset cloneData).entries[map.entries.size]'(by rw [length];omega)).range.stop := by
    simpa only [length,Nat.add_sub_cancel] using last
  exact lastEq.trans ((stop_right map position valid offset cloneData map.entries.size (by omega) (by omega)).trans
    (size_last map (by omega)).symm)

theorem every (predicate : α → Prop) (map : DedupRangeMap α) (position : Nat) (valid : position < map.entries.size)
    (offset : UInt64) (cloneData : α → α) (all : Every predicate map)
    (cloneGood : ∀ data, predicate data → predicate (cloneData data)) :
    Every predicate (splitMap map position valid offset cloneData) := by
  intro index bounded
  have sizeBound : index ≤ map.entries.size := by rw [length] at bounded;omega
  by_cases second : index = position+1
  · subst index
    dsimp only [splitMap]
    rw [Array.getElem_insertIdx_self]
    exact cloneGood _ (all position valid)
  · by_cases left : index ≤ position
    · dsimp only [splitMap]
      rw [Array.getElem_insertIdx_of_lt _ (by omega)]
      by_cases same : position = index
      · subst index
        rw [Array.getElem_set_self]
        exact all position valid
      · rw [Array.getElem_set_ne _ (by omega) same]
        exact all index (by omega)
    · dsimp only [splitMap]
      rw [Array.getElem_insertIdx_of_gt (by simpa only [Array.size_set] using sizeBound) (by omega)]
      rw [Array.getElem_set_ne _ (by omega) (by omega)]
      exact all (index-1) (by omega)

theorem actual_boundary (map : DedupRangeMap α) (position : Nat) (valid : position < map.entries.size)
    (offset : UInt64) (cloneData : α → α)
    (edge : offset = map.entries[position].range.start ∨ offset = map.entries[position].range.stop) :
    range_split_index map.entries position offset cloneData = .ok (map.entries,false) := by
  simp_range_helpers
  rcases edge with rfl | rfl <;> simp [valid]

theorem prepare_start (predicate : α → Prop) (map : DedupRangeMap α)
    (position : Nat) (valid : position < map.entries.size) (offset : UInt64) (cloneData : α → α)
    (good : map.WellFormed) (all : Every predicate map) (cloneGood : ∀ data, predicate data → predicate (cloneData data))
    (afterStart : map.entries[position].range.start ≤ offset) (beforeEnd : offset < map.entries[position].range.stop) :
    ∃ current : DedupRangeMap α, ∃ didSplit : Bool,
      range_split_index map.entries position offset cloneData = .ok (current.entries,didSplit) ∧
      current.WellFormed ∧ current.size.bytes = map.size.bytes ∧ Every predicate current ∧
      ∃ bounded : position+(if didSplit then 1 else 0) < current.entries.size,
        (current.entries[position+(if didSplit then 1 else 0)]).range.start = offset ∧
        (current.entries[position+(if didSplit then 1 else 0)]).range.stop = map.entries[position].range.stop := by
  by_cases same : offset = map.entries[position].range.start
  · refine ⟨map,false,actual_boundary map position valid offset cloneData (.inl same),good,rfl,all,?_,?_,?_⟩
    · simpa using valid
    · simpa using same.symm
    · rfl
  · have strict : map.entries[position].range.start < offset := by
      simp only [UInt64.le_iff_toNat_le] at afterStart
      have unequal : offset.toNat ≠ map.entries[position].range.start.toNat := fun h => same (UInt64.toNat_inj.mp h)
      apply UInt64.lt_iff_toNat_lt.mpr
      omega
    refine ⟨splitMap map position valid offset cloneData,true,
      actual_inside map position valid offset cloneData strict beforeEnd,
      wellFormed map position valid offset cloneData good strict beforeEnd,
      size_bytes map position valid offset cloneData,every predicate map position valid offset cloneData all cloneGood,?_,?_,?_⟩
    · rw [length]
      simp only [↓reduceIte]
      omega
    · exact start_second map position valid offset cloneData
    · simpa only [Nat.add_sub_cancel,↓reduceIte] using stop_right map position valid offset cloneData (position+1) (by omega) (by omega)

theorem prepare_end (predicate : α → Prop) (map : DedupRangeMap α)
    (position : Nat) (valid : position < map.entries.size) (offset : UInt64) (cloneData : α → α)
    (good : map.WellFormed) (all : Every predicate map) (cloneGood : ∀ data, predicate data → predicate (cloneData data))
    (afterStart : map.entries[position].range.start < offset) (beforeEnd : offset ≤ map.entries[position].range.stop) :
    ∃ current : DedupRangeMap α, ∃ didSplit : Bool,
      range_split_index map.entries position offset cloneData = .ok (current.entries,didSplit) ∧
      current.WellFormed ∧ current.size.bytes = map.size.bytes ∧ Every predicate current ∧
      ∃ bounded : position < current.entries.size,
        (current.entries[position]).range.stop = offset := by
  by_cases same : offset = map.entries[position].range.stop
  · exact ⟨map,false,actual_boundary map position valid offset cloneData (.inr same),good,rfl,all,valid,same.symm⟩
  · have strict : offset < map.entries[position].range.stop := by
      simp only [UInt64.le_iff_toNat_le] at beforeEnd
      have unequal : offset.toNat ≠ map.entries[position].range.stop.toNat := fun h => same (UInt64.toNat_inj.mp h)
      apply UInt64.lt_iff_toNat_lt.mpr
      omega
    exact ⟨splitMap map position valid offset cloneData,true,
      actual_inside map position valid offset cloneData afterStart strict,
      wellFormed map position valid offset cloneData good afterStart strict,
      size_bytes map position valid offset cloneData,every predicate map position valid offset cloneData all cloneGood,
      by rw [length];omega,stop_first map position valid offset cloneData⟩

end DuplicatePrefix.GeneralRangeMapSplit
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralRangeMapSplit." then
      for dependency in (←collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved general range split axiom {dependency}"
