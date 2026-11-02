import duplicate_prefix.GeneralRangeMapMerge
namespace DuplicatePrefix.GeneralRangeMapOrigins
open Miri Miri.ABI Miri.DataStructures
open DuplicatePrefix.GeneralRangeMapGeometry
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- One stored segment supplies a raw value at the given byte position. -/
def ValueAt (map : DedupRangeMap α) (point : UInt64) (value : α) : Prop :=
  ∃ position, ∃ valid : position < map.entries.size,
    map.entries[position].range.start.toNat ≤ point.toNat ∧
    point.toNat < map.entries[position].range.stop.toNat ∧ map.entries[position].data = value

/-- Every pointwise value in the prepared map has an original-map witness.
This relation permits merging several adjacent segments with equal raw data. -/
def Refines (original prepared : DedupRangeMap α) : Prop :=
  ∀ point value, ValueAt prepared point value → ValueAt original point value

theorem reflexive (map : DedupRangeMap α) : Refines map map := fun _ _ value => value

theorem transitive (first middle last : DedupRangeMap α)
    (before : Refines first middle) (after : Refines middle last) : Refines first last :=
  fun point value witness => before point value (after point value witness)

/-- The actual split with a value-preserving clone retains every pointwise
value. The cut bounds are data conditions, not a split-success premise. -/
theorem split_refines (map : DedupRangeMap α) (position : Nat)
    (valid : position < map.entries.size) (cut : UInt64)
    (afterStart : map.entries[position].range.start ≤ cut)
    (beforeStop : cut ≤ map.entries[position].range.stop) :
    Refines map (GeneralRangeMapSplit.splitMap map position valid cut id) := by
  intro point value witness
  rcases witness with ⟨index,bounded,start,stop,data⟩
  have maxIndex : index ≤ map.entries.size := by
    rw [GeneralRangeMapSplit.length] at bounded
    omega
  have startCut := UInt64.le_iff_toNat_le.mp afterStart
  have cutStop := UInt64.le_iff_toNat_le.mp beforeStop
  by_cases second : index = position+1
  · subst index
    dsimp only [GeneralRangeMapSplit.splitMap] at start stop data
    rw [Array.getElem_insertIdx_self] at start stop data
    exact ⟨position,valid,by dsimp only at start;omega,by simpa using stop,by simpa using data⟩
  · by_cases left : index ≤ position
    · dsimp only [GeneralRangeMapSplit.splitMap] at start stop data
      rw [Array.getElem_insertIdx_of_lt _ (by omega)] at start stop data
      by_cases same : position = index
      · subst index
        rw [Array.getElem_set_self] at start stop data
        exact ⟨position,valid,by simpa using start,by dsimp only at stop;omega,by simpa using data⟩
      · rw [Array.getElem_set_ne _ (by omega) same] at start stop data
        exact ⟨index,by omega,start,stop,data⟩
    · dsimp only [GeneralRangeMapSplit.splitMap] at start stop data
      rw [Array.getElem_insertIdx_of_gt (by simpa only [Array.size_set] using maxIndex) (by omega)] at start stop data
      rw [Array.getElem_set_ne _ (by omega) (by omega)] at start stop data
      exact ⟨index-1,by omega,start,stop,data⟩

/-- Equal-data adjacency allows the real merge-run mutation to preserve every
raw value at every byte position, including runs spanning multiple old segments. -/
theorem merge_refines (map : DedupRangeMap α) (first stop : Nat)
    (ordered : first < stop) (bounded : stop ≤ map.entries.size) (well : map.WellFormed)
    (equal : ∀ position (atFirst : first ≤ position) (beforeStop : position < stop),
      (map.entries[position]'(by omega)).data = (map.entries[first]'(by omega)).data) :
    Refines map (GeneralRangeMapMerge.mergeMap map first stop ordered bounded) := by
  intro point value witness
  rcases witness with ⟨index,valid,start,finish,data⟩
  by_cases left : index < first
  · rw [GeneralRangeMapMerge.start_left map first stop ordered bounded index (by omega)] at start
    rw [GeneralRangeMapMerge.stop_left map first stop ordered bounded index left] at finish
    rw [GeneralRangeMapMerge.data_left map first stop ordered bounded index (by omega)] at data
    exact ⟨index,by omega,start,finish,data⟩
  · by_cases same : index = first
    · subst index
      rw [GeneralRangeMapMerge.start_left map first stop ordered bounded first (by omega)] at start
      rw [GeneralRangeMapMerge.stop_first map first stop ordered bounded] at finish
      rw [GeneralRangeMapMerge.data_left map first stop ordered bounded first (by omega)] at data
      obtain ⟨original,beforeLast,oldValid,oldStart,oldStop⟩ :=
        contains_before map well point (stop-1) (by omega) finish
      have lower : first ≤ original := by
        by_cases inside : first ≤ original
        · exact inside
        · have earlier : original < first := by omega
          have separation := stop_le_start map well original first earlier (by omega)
          omega
      exact ⟨original,oldValid,oldStart,oldStop,(equal original lower (by omega)).trans data⟩
    · have after : first < index := by omega
      rw [GeneralRangeMapMerge.range_right map first stop ordered bounded index after valid] at start finish data
      exact ⟨index+(stop-first-1),by rw [GeneralRangeMapMerge.length] at valid;omega,start,finish,data⟩


/-- The source split's successful result and its pointwise relation are both
conclusions; no mutation outcome is supplied by the caller. -/
theorem split_actual (map : DedupRangeMap α) (position : Nat)
    (valid : position < map.entries.size) (cut : UInt64)
    (afterStart : map.entries[position].range.start < cut)
    (beforeStop : cut < map.entries[position].range.stop) :
    ∃ next, range_split_index map.entries position cut id = .ok (next.entries,true) ∧ Refines map next := by
  refine ⟨GeneralRangeMapSplit.splitMap map position valid cut id,
    GeneralRangeMapSplit.actual_inside map position valid cut id afterStart beforeStop,?_⟩
  exact split_refines map position valid cut
    (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp afterStart)))
    (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp beforeStop)))

/-- The real merge-run call completes and retains all pointwise raw values
under the data equality established by the iterator's equal-run invariant. -/
theorem merge_actual (map : DedupRangeMap α) (first stop : Nat)
    (ordered : first < stop) (bounded : stop ≤ map.entries.size) (well : map.WellFormed)
    (equal : ∀ position (atFirst : first ≤ position) (beforeStop : position < stop),
      (map.entries[position]'(by omega)).data = (map.entries[first]'(by omega)).data) :
    ∃ next, range_merge_run map.entries first stop = .ok next.entries ∧ Refines map next :=
  ⟨GeneralRangeMapMerge.mergeMap map first stop ordered bounded,
    GeneralRangeMapMerge.actual map first stop ordered bounded,
    merge_refines map first stop ordered bounded well equal⟩

/-- A range-local data contract. Empty slices impose no ownership condition;
for positive slices only overlapping stored segments need the property. -/
def OwnedOn (predicate : α → Prop) (lower upper : UInt64) (map : DedupRangeMap α) : Prop :=
  ∀ position (valid : position < map.entries.size), lower.toNat < upper.toNat →
    map.entries[position].range.start.toNat < upper.toNat →
    lower.toNat < map.entries[position].range.stop.toNat → predicate map.entries[position].data

/-- Pointwise preparation preserves a slice-local data contract, without any
condition on segments disjoint from that slice. Splits and equal-data merges
may change segmentation; the proof selects a byte in the overlap. -/
theorem refines_owned_on (original prepared : DedupRangeMap α) (predicate : α → Prop)
    (lower upper : UInt64) (well : prepared.WellFormed) (refined : Refines original prepared)
    (owned : OwnedOn predicate lower upper original) : OwnedOn predicate lower upper prepared := by
  intro position valid positive beforeUpper afterLower
  have segmentPositive := (facts prepared well (by omega)).2.1 position valid
  have transfer : ∀ point : UInt64, lower.toNat ≤ point.toNat → point.toNat < upper.toNat →
      prepared.entries[position].range.start.toNat ≤ point.toNat →
      point.toNat < prepared.entries[position].range.stop.toNat → predicate prepared.entries[position].data := by
    intro point inLower inUpper inStart inStop
    obtain ⟨origin,bounded,oldStart,oldStop,same⟩ := refined point prepared.entries[position].data
      ⟨position,valid,inStart,inStop,rfl⟩
    have before := owned origin bounded positive (by omega) (by omega)
    simpa only [same] using before
  by_cases earlier : lower.toNat ≤ prepared.entries[position].range.start.toNat
  · exact transfer prepared.entries[position].range.start earlier beforeUpper (by omega) segmentPositive
  · exact transfer lower (by omega) positive (by omega) afterLower



/-- A selected-segment data bridge for a prepared iterator. The premises are
only array membership, interval containment, well-formedness and pointwise
origins; no successful range preparation is assumed. The actual iterator must
still prove these data facts and its outcome separately. -/
theorem selected_owned (original : DedupRangeMap α) (prepared : IterMutResult α)
    (predicate : α → Prop) (lower upper : UInt64) (well : prepared.state.WellFormed)
    (refined : Refines original prepared.state) (owned : OwnedOn predicate lower upper original)
    (selected : ∀ cursor (valid : cursor < prepared.segments.size),
      ∃ position, ∃ bounded : position < prepared.state.entries.size,
        prepared.segments[cursor] = prepared.state.entries[position])
    (within : ∀ cursor (valid : cursor < prepared.segments.size),
      lower.toNat ≤ prepared.segments[cursor].range.start.toNat ∧
        prepared.segments[cursor].range.stop.toNat ≤ upper.toNat) :
    ∀ cursor (valid : cursor < prepared.segments.size), predicate prepared.segments[cursor].data := by
  have transported := refines_owned_on original prepared.state predicate lower upper well refined owned
  intro cursor valid
  obtain ⟨position,bounded,same⟩ := selected cursor valid
  have inside := within cursor valid
  rw [same] at inside ⊢
  have positive := (facts prepared.state well (by omega)).2.1 position bounded
  exact transported position bounded (by omega) (by omega) (by omega)


end DuplicatePrefix.GeneralRangeMapOrigins
#print axioms DuplicatePrefix.GeneralRangeMapOrigins.split_refines
#print axioms DuplicatePrefix.GeneralRangeMapOrigins.merge_refines
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralRangeMapOrigins." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved pointwise range-origin dependency {dependency}"
