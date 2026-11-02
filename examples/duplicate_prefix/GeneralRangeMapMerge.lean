import duplicate_prefix.GeneralRangeMapSplit
namespace DuplicatePrefix.GeneralRangeMapMerge
open Miri Miri.ABI Miri.DataStructures
open DuplicatePrefix.RangeMapNonempty GeneralRangeMapState GeneralRangeMapGeometry
open Lean Elab Tactic
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
elab "range_merge_run" : term => do
  let candidates := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".DedupRangeMap.mergeRun" then some name else none
  match candidates with
  | [name] => return mkConst name
  | _ => throwError "expected unique actual mergeRun"
elab "simp_range_merge_source" : tactic => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if [".DedupRangeMap.mergeRun",".DedupRangeMap.removeInterval",".DedupRangeMap.segmentAt?",".DedupRangeMap.updateAt"].any (fun suffix => name.toString.endsWith suffix) then some (mkIdent name) else none
  let names := names.toArray
  evalTactic (← `(tactic| simp only [$[$names:ident],*]))

def head (map : DedupRangeMap α) (first stop : Nat) (ordered : first < stop) (bounded : stop ≤ map.entries.size) : RangeMapSegment α :=
  {(map.entries[first]'(by omega)) with range := {(map.entries[first]'(by omega)).range with stop := (map.entries[stop-1]'(by omega)).range.stop}}
def updated (map : DedupRangeMap α) (first stop : Nat) (ordered : first < stop) (bounded : stop ≤ map.entries.size) :=
  map.entries.set first (head map first stop ordered bounded) (by omega)
def mergeMap (map : DedupRangeMap α) (first stop : Nat) (ordered : first < stop) (bounded : stop ≤ map.entries.size) : DedupRangeMap α :=
  ⟨(updated map first stop ordered bounded).extract 0 (first+1) ++
    (updated map first stop ordered bounded).extract stop map.entries.size⟩

theorem actual (map : DedupRangeMap α) (first stop : Nat) (ordered : first < stop) (bounded : stop ≤ map.entries.size) :
    range_merge_run map.entries first stop = .ok (mergeMap map first stop ordered bounded).entries := by
  have firstValid : first < map.entries.size := by omega
  have lastValid : stop-1 < map.entries.size := by omega
  simp_range_merge_source
  simp [firstValid,lastValid,updated,head,mergeMap,bind,Except.bind,pure,Except.pure]

theorem prefix_size (map : DedupRangeMap α) (first stop : Nat) (ordered : first < stop) (bounded : stop ≤ map.entries.size) :
    ((updated map first stop ordered bounded).extract 0 (first+1)).size = first+1 := by
  simp only [Array.size_extract,updated,Array.size_set]
  omega

theorem length (map : DedupRangeMap α) (first stop : Nat) (ordered : first < stop) (bounded : stop ≤ map.entries.size) :
    (mergeMap map first stop ordered bounded).entries.size = map.entries.size-(stop-first-1) := by
  simp only [mergeMap,Array.size_append,Array.size_extract,updated,Array.size_set]
  omega

theorem start_left (map : DedupRangeMap α) (first stop : Nat) (ordered : first < stop) (bounded : stop ≤ map.entries.size)
    (index : Nat) (before : index ≤ first) :
    ((mergeMap map first stop ordered bounded).entries[index]'(by rw [length];omega)).range.start =
      (map.entries[index]'(by omega)).range.start := by
  dsimp only [mergeMap]
  rw [Array.getElem_append_left (by rw [prefix_size];omega),Array.getElem_extract]
  simp only [Nat.zero_add,updated]
  by_cases same : first = index
  · subst index
    rw [Array.getElem_set_self]
    rfl
  · rw [Array.getElem_set_ne _ (by omega) same]

theorem stop_left (map : DedupRangeMap α) (first stop : Nat) (ordered : first < stop) (bounded : stop ≤ map.entries.size)
    (index : Nat) (before : index < first) :
    ((mergeMap map first stop ordered bounded).entries[index]'(by rw [length];omega)).range.stop =
      (map.entries[index]'(by omega)).range.stop := by
  dsimp only [mergeMap]
  rw [Array.getElem_append_left (by rw [prefix_size];omega),Array.getElem_extract]
  simp only [Nat.zero_add,updated]
  rw [Array.getElem_set_ne _ (by omega) (by omega)]

theorem stop_first (map : DedupRangeMap α) (first stop : Nat) (ordered : first < stop) (bounded : stop ≤ map.entries.size) :
    ((mergeMap map first stop ordered bounded).entries[first]'(by rw [length];omega)).range.stop =
      (map.entries[stop-1]'(by omega)).range.stop := by
  dsimp only [mergeMap]
  rw [Array.getElem_append_left (by rw [prefix_size];omega),Array.getElem_extract]
  simp only [Nat.zero_add,updated,Array.getElem_set_self,head]

theorem range_right (map : DedupRangeMap α) (first stop : Nat) (ordered : first < stop) (bounded : stop ≤ map.entries.size)
    (index : Nat) (after : first < index) (valid : index < (mergeMap map first stop ordered bounded).entries.size) :
    (mergeMap map first stop ordered bounded).entries[index] =
      (map.entries[index+(stop-first-1)]'(by rw [length] at valid;omega)) := by
  have sizeValid : index < map.entries.size-(stop-first-1) := by simpa only [length] using valid
  dsimp only [mergeMap] at valid ⊢
  rw [Array.getElem_append_right (by rw [prefix_size];omega),Array.getElem_extract]
  simp only [prefix_size]
  have shift : stop+(index-(first+1)) = index+(stop-first-1) := by omega
  simp only [shift]
  dsimp only [updated]
  rw [Array.getElem_set_ne _ (by omega) (by omega)]

theorem data_left (map : DedupRangeMap α) (first stop : Nat) (ordered : first < stop) (bounded : stop ≤ map.entries.size)
    (index : Nat) (before : index ≤ first) :
    ((mergeMap map first stop ordered bounded).entries[index]'(by rw [length];omega)).data =
      (map.entries[index]'(by omega)).data := by
  dsimp only [mergeMap]
  rw [Array.getElem_append_left (by rw [prefix_size];omega),Array.getElem_extract]
  simp only [Nat.zero_add,updated]
  by_cases same : first = index
  · subst index
    rw [Array.getElem_set_self]
    rfl
  · rw [Array.getElem_set_ne _ (by omega) same]

theorem every (predicate : α → Prop) (map : DedupRangeMap α) (first stop : Nat)
    (ordered : first < stop) (bounded : stop ≤ map.entries.size) (all : Every predicate map) :
    Every predicate (mergeMap map first stop ordered bounded) := by
  intro index valid
  by_cases left : index ≤ first
  · rw [data_left map first stop ordered bounded index left]
    exact all index (by omega)
  · rw [range_right map first stop ordered bounded index (by omega) valid]
    exact all (index+(stop-first-1)) (by rw [length] at valid;omega)

theorem wellFormed (map : DedupRangeMap α) (first stop : Nat)
    (ordered : first < stop) (bounded : stop ≤ map.entries.size) (good : map.WellFormed) :
    (mergeMap map first stop ordered bounded).WellFormed := by
  have oldNonempty : map.entries.size ≠ 0 := by omega
  have state : (map.entries[0]'(by omega)).range.start = 0 ∧
      (∀ index (valid : index < map.entries.size), map.entries[index].range.start < map.entries[index].range.stop) ∧
      (∀ index (valid : index+1 < map.entries.size), map.entries[index].range.stop = map.entries[index+1].range.start) := by
    simpa only [DedupRangeMap.WellFormed,oldNonempty,↓reduceDIte] using good
  have newNonempty : (mergeMap map first stop ordered bounded).entries.size ≠ 0 := by rw [length];omega
  simp only [DedupRangeMap.WellFormed,newNonempty,↓reduceDIte]
  refine ⟨?_,?_,?_⟩
  · rw [start_left map first stop ordered bounded 0 (by omega)]
    exact state.1
  · intro index valid
    have sizeValid : index < map.entries.size-(stop-first-1) := by simpa only [length] using valid
    by_cases left : index < first
    · rw [start_left map first stop ordered bounded index (by omega),stop_left map first stop ordered bounded index left]
      exact state.2.1 index (by omega)
    · by_cases same : index = first
      · subst index
        rw [start_left map first stop ordered bounded first (by omega),stop_first]
        by_cases one : stop-1 = first
        · simpa only [one] using state.2.1 first (by omega)
        · have further : first < stop-1 := by omega
          have between := stop_le_start map good first (stop-1) further (by omega)
          have firstPositive := UInt64.lt_iff_toNat_lt.mp (state.2.1 first (by omega))
          have lastPositive := UInt64.lt_iff_toNat_lt.mp (state.2.1 (stop-1) (by omega))
          apply UInt64.lt_iff_toNat_lt.mpr
          omega
      · rw [range_right map first stop ordered bounded index (by omega) valid]
        exact state.2.1 (index+(stop-first-1)) (by omega)
  · intro index valid
    have sizeValid : index+1 < map.entries.size-(stop-first-1) := by simpa only [length] using valid
    by_cases left : index < first
    · rw [stop_left map first stop ordered bounded index left,start_left map first stop ordered bounded (index+1) (by omega)]
      exact state.2.2 index (by omega)
    · by_cases same : index = first
      · subst index
        rw [stop_first,range_right map first stop ordered bounded (first+1) (by omega) valid]
        have shift : first+1+(stop-first-1) = stop := by omega
        have adjacent := state.2.2 (stop-1) (by omega)
        simpa only [shift,Nat.sub_add_cancel (by omega : 1 ≤ stop)] using adjacent
      · have oldValid : index < (mergeMap map first stop ordered bounded).entries.size := by omega
        rw [range_right map first stop ordered bounded index (by omega) oldValid,
          range_right map first stop ordered bounded (index+1) (by omega) valid]
        have shift : index+1+(stop-first-1) = (index+(stop-first-1))+1 := by omega
        simpa only [shift] using state.2.2 (index+(stop-first-1)) (by omega)

theorem size_bytes (map : DedupRangeMap α) (first stop : Nat)
    (ordered : first < stop) (bounded : stop ≤ map.entries.size) :
    (mergeMap map first stop ordered bounded).size.bytes = map.size.bytes := by
  let result := mergeMap map first stop ordered bounded
  have nonempty : 0 < result.entries.size := by dsimp only [result];rw [length];omega
  have resultLast := size_last result nonempty
  have oldLast := size_last map (by omega)
  by_cases terminal : stop = map.entries.size
  · have lastEq : result.entries.size-1 = first := by dsimp only [result];rw [length];omega
    have resultLast' : result.size.bytes = (result.entries[first]'(by omega)).range.stop := by simpa only [lastEq] using resultLast
    have originalStop : (map.entries[stop-1]'(by omega)).range.stop = map.size.bytes := by simpa only [terminal] using oldLast.symm
    exact resultLast'.trans ((stop_first map first stop ordered bounded).trans originalStop)
  · have after : first < result.entries.size-1 := by dsimp only [result];rw [length];omega
    have valid : result.entries.size-1 < result.entries.size := by omega
    have same := range_right map first stop ordered bounded (result.entries.size-1) after valid
    have shift : result.entries.size-1+(stop-first-1) = map.entries.size-1 := by dsimp only [result];rw [length];omega
    have stops : (result.entries[result.entries.size-1]'valid).range.stop = (map.entries[map.entries.size-1]'(by omega)).range.stop := by
      simpa only [shift] using congrArg (fun entry : RangeMapSegment α => entry.range.stop) same
    exact resultLast.trans (stops.trans oldLast.symm)

end DuplicatePrefix.GeneralRangeMapMerge
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralRangeMapMerge." then
      for dependency in (←collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved general range merge axiom {dependency}"
