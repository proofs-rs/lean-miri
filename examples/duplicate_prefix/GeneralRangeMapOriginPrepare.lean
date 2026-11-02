import duplicate_prefix.GeneralRangeMapOriginScan
import duplicate_prefix.GeneralRangeMapPrepared
namespace DuplicatePrefix.GeneralRangeMapOriginPrepare
open Miri Miri.ABI Miri.DataStructures
open DuplicatePrefix.RangeMapNonempty GeneralRangeMapState GeneralRangeMapGeometry GeneralRangeMapOrigins
open GeneralRangeMapScan GeneralRangeMapPrepare
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- The start split's complete source/data contract for an identity clone. -/
theorem start_data (map : DedupRangeMap α) (position : Nat) (valid : position < map.entries.size)
    (cut : UInt64) (well : map.WellFormed)
    (afterStart : map.entries[position].range.start ≤ cut) (beforeStop : cut < map.entries[position].range.stop) :
    ∃ current : DedupRangeMap α, ∃ didSplit : Bool,
      range_split_index map.entries position cut id = .ok (current.entries,didSplit) ∧
      current.WellFormed ∧ current.size.bytes = map.size.bytes ∧ Refines map current ∧
      ∃ bounded : position+(if didSplit then 1 else 0) < current.entries.size,
        current.entries[position+(if didSplit then 1 else 0)].range.start = cut ∧
        current.entries[position+(if didSplit then 1 else 0)].range.stop = map.entries[position].range.stop := by
  by_cases same : cut = map.entries[position].range.start
  · exact ⟨map,false,GeneralRangeMapSplit.actual_boundary map position valid cut id (.inl same),
      well,rfl,reflexive map,by simpa using valid,by simpa using same.symm,rfl⟩
  · have strict : map.entries[position].range.start < cut := by
      simp only [UInt64.le_iff_toNat_le] at afterStart
      have unequal : cut.toNat ≠ map.entries[position].range.start.toNat := fun h => same (UInt64.toNat_inj.mp h)
      apply UInt64.lt_iff_toNat_lt.mpr
      omega
    refine ⟨GeneralRangeMapSplit.splitMap map position valid cut id,true,
      GeneralRangeMapSplit.actual_inside map position valid cut id strict beforeStop,
      GeneralRangeMapSplit.wellFormed map position valid cut id well strict beforeStop,
      GeneralRangeMapSplit.size_bytes map position valid cut id,
      split_refines map position valid cut afterStart (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp beforeStop))),?_,?_,?_⟩
    · rw [GeneralRangeMapSplit.length]
      simp only [↓reduceIte]
      omega
    · exact GeneralRangeMapSplit.start_second map position valid cut id
    · simpa only [Nat.add_sub_cancel,↓reduceIte] using
        GeneralRangeMapSplit.stop_right map position valid cut id (position+1) (by omega) (by omega)

/-- The end split preserves all earlier starts while retaining pointwise origins. -/
theorem end_data (map : DedupRangeMap α) (position : Nat) (valid : position < map.entries.size)
    (cut : UInt64) (well : map.WellFormed)
    (afterStart : map.entries[position].range.start < cut) (beforeStop : cut ≤ map.entries[position].range.stop) :
    ∃ current : DedupRangeMap α, ∃ didSplit : Bool,
      range_split_index map.entries position cut id = .ok (current.entries,didSplit) ∧
      current.WellFormed ∧ current.size.bytes = map.size.bytes ∧ Refines map current ∧
      ∃ bounded : position < current.entries.size,
        current.entries[position].range.stop = cut ∧
        ∀ index (earlier : index ≤ position),
          (current.entries[index]'(by omega)).range.start = (map.entries[index]'(by omega)).range.start := by
  by_cases same : cut = map.entries[position].range.stop
  · exact ⟨map,false,GeneralRangeMapSplit.actual_boundary map position valid cut id (.inr same),
      well,rfl,reflexive map,valid,same.symm,fun _ _ => rfl⟩
  · have strict : cut < map.entries[position].range.stop := by
      simp only [UInt64.le_iff_toNat_le] at beforeStop
      have unequal : cut.toNat ≠ map.entries[position].range.stop.toNat := fun h => same (UInt64.toNat_inj.mp h)
      apply UInt64.lt_iff_toNat_lt.mpr
      omega
    exact ⟨GeneralRangeMapSplit.splitMap map position valid cut id,true,
      GeneralRangeMapSplit.actual_inside map position valid cut id afterStart strict,
      GeneralRangeMapSplit.wellFormed map position valid cut id well afterStart strict,
      GeneralRangeMapSplit.size_bytes map position valid cut id,
      split_refines map position valid cut (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp afterStart))) beforeStop,
      by rw [GeneralRangeMapSplit.length];omega,
      GeneralRangeMapSplit.stop_first map position valid cut id,
      fun index earlier => GeneralRangeMapSplit.start_left map position valid cut id index earlier⟩

/-- Every selected segment lies wholly in the requested half-open interval. -/
def Within (result : IterMutResult α) (lower upper : UInt64) : Prop :=
  ∀ cursor (valid : cursor < result.segments.size),
    lower.toNat ≤ result.segments[cursor].range.start.toNat ∧ result.segments[cursor].range.stop.toNat ≤ upper.toNat

private theorem window_bounds (map : DedupRangeMap α) (first stop : Nat)
    (ordered : first < stop) (bounded : stop ≤ map.entries.size) (well : map.WellFormed)
    (lower upper : UInt64) (start : (map.entries[first]'(by omega)).range.start = lower)
    (finish : (map.entries[stop-1]'(by omega)).range.stop = upper) :
    ∀ cursor (valid : cursor < (map.entries.extract first stop).size),
      lower.toNat ≤ (map.entries.extract first stop)[cursor].range.start.toNat ∧
      (map.entries.extract first stop)[cursor].range.stop.toNat ≤ upper.toNat := by
  intro cursor valid
  have cursorBound : first+cursor < stop := by
    simp only [Array.size_extract] at valid
    omega
  rw [Array.getElem_extract]
  have positive := (facts map well (by omega)).2.1
  constructor
  · by_cases same : first+cursor = first
    · simpa only [same,start] using (Nat.le_refl lower.toNat)
    · have separation := stop_le_start map well first (first+cursor) (by omega) (by omega)
      have strict := positive first (by omega)
      rw [start] at strict
      omega
  · by_cases same : first+cursor = stop-1
    · simpa only [same,finish] using (Nat.le_refl upper.toNat)
    · have separation := stop_le_start map well (first+cursor) (stop-1) (by omega) (by omega)
      have strict := positive (stop-1) (by omega)
      rw [finish] at strict
      omega

/-- Finish the real prepared result after a completed scan, retaining both
pointwise origins and the selected window's geometry. -/
theorem finish_data (original : DedupRangeMap α) (offset finish capacity : UInt64) (first : Nat)
    (state : State α) (good : GeneralRangeMapScanSafety.Good (fun _ => True) offset finish capacity first state)
    (done : state.2.2.2.2.1 = true) (refined : Refines original state.1) :
    let result := finishPrepared first finish id state
    GeneralRangeMapPrepared.Good (fun _ => True) capacity result ∧ Refines original result.state ∧ Within result offset finish := by
  dsimp only
  rcases state with ⟨map,equal,count,index,active,failure⟩
  dsimp only at done refined
  subst active
  simp only [GeneralRangeMapScanSafety.Good,↓reduceIte] at good
  rcases good with ⟨well,all,cap,failureEq,firstLE,equalLE,indexLE,firstValid,start,lastValid,firstLT,startFinish,finishStop⟩
  subst failure
  obtain ⟨current,didSplit,split,currentWell,currentCap,currentRef,lastNew,stopFinish,prefixStarts⟩ :=
    end_data map (index-1) lastValid finish well
      (UInt64.lt_iff_toNat_lt.mpr startFinish) (UInt64.le_iff_toNat_le.mpr finishStop)
  have positive : 0 < index := by omega
  have newBound : index ≤ current.entries.size := by omega
  have ordered : first < index := firstLT
  have currentStart : (current.entries[first]'(by omega)).range.start = offset :=
    (prefixStarts first (by omega)).trans start
  have sourceSelected := GeneralRangeMapPrepared.selected_exact current first index (by omega) newBound
  unfold finishPrepared
  simp only [Id.run,bind,pure]
  rw [split]
  dsimp only
  have indexEq : index-1+1 = index := by omega
  rw [indexEq,sourceSelected]
  refine ⟨GeneralRangeMapPrepared.explicit_good (fun _ => True) capacity current first index (by omega) newBound
    currentWell (fun _ _ => True.intro) (currentCap.trans cap),transitive original map current refined currentRef,?_⟩
  exact window_bounds current first index ordered newBound currentWell offset finish currentStart stopFinish

/-- Actual identity-clone range preparation completes while preserving raw
pointwise values and selecting only requested bytes. These facts support a
slice-local ownership contract, without restricting disjoint original segments. -/
theorem iter_mut [DecidableEq α] (map : DedupRangeMap α) (offset len : Size)
    (well : map.WellFormed) (bounds : offset.bytes.toNat + len.bytes.toNat ≤ map.size.bytes.toNat) :
    let result := map.iterMut offset len
    GeneralRangeMapPrepared.Good (fun _ => True) map.size.bytes result ∧
      Refines map result.state ∧ Within result offset.bytes (offset.bytes+len.bytes) := by
  dsimp only
  unfold DedupRangeMap.iterMut
  by_cases empty : len.bytes = 0
  · have actual : map.iterMutWithClone offset len id = ⟨map,#[],#[],.ok ()⟩ := by
      simp [DedupRangeMap.iterMutWithClone,empty]
    rw [actual]
    refine ⟨⟨rfl,well,fun _ _ => True.intro,rfl,rfl,?_⟩,reflexive map,?_⟩
    · intro cursor valid
      simp at valid
    · intro cursor valid
      simp at valid
  · have positive : 0 < len.bytes.toNat := by
      have unequal : len.bytes.toNat ≠ 0 := by
        intro zero
        exact empty (UInt64.toNat_inj.mp zero)
      omega
    have inside : offset.bytes.toNat < map.size.bytes.toNat := by omega
    have fits : offset.bytes.toNat+len.bytes.toNat < 2^64 := Nat.lt_of_le_of_lt bounds map.size.bytes.toNat_lt
    have finishNat : (offset.bytes+len.bytes).toNat = offset.bytes.toNat+len.bytes.toNat := by
      simp only [UInt64.toNat_add,Nat.mod_eq_of_lt fits]
    have calculated := checked_end_add offset.bytes len.bytes fits
    obtain ⟨first,search,firstValid,afterStart,beforeEnd⟩ := GeneralRangeMapFind.find_success map offset.bytes well inside
    obtain ⟨start,didSplit,split,startWell,startCap,startRef,startValid,startAt,startStop⟩ :=
      start_data map first firstValid offset.bytes well (UInt64.le_iff_toNat_le.mpr afterStart) (UInt64.lt_iff_toNat_lt.mpr beforeEnd)
    let beginning := if didSplit then first+1 else first
    have beginValid : beginning < start.entries.size := by cases didSplit <;> simpa [beginning] using startValid
    have beginAt : (start.entries[beginning]'beginValid).range.start = offset.bytes := by cases didSplit <;> simpa [beginning] using startAt
    let initial : State α := (start,beginning,3,beginning,false,none)
    have initialGood : GeneralRangeMapScanSafety.Good (fun _ => True) offset.bytes (offset.bytes+len.bytes) map.size.bytes beginning initial := by
      dsimp only [GeneralRangeMapScanSafety.Good,initial]
      refine ⟨startWell,fun _ _ => True.intro,startCap,rfl,by omega,by omega,by omega,beginValid,beginAt,?_⟩
      simp only [Bool.false_eq_true,↓reduceIte]
      refine ⟨beginValid,?_⟩
      rw [beginAt,finishNat]
      omega
    have initialOrigins : GeneralRangeMapOriginScan.OriginState map initial := by
      refine ⟨startRef,?_⟩
      intro _ _
      change GeneralRangeMapOriginScan.EqualRun start beginning beginning
      intro position valid lower upper
      have same : position = beginning := by omega
      subst position
      rfl
    have finishInside : (offset.bytes+len.bytes).toNat ≤ map.size.bytes.toNat := by rw [finishNat];exact bounds
    have final := GeneralRangeMapOriginScan.finishes map offset.bytes (offset.bytes+len.bytes) map.size.bytes beginning
      finishInside initial initialGood initialOrigins
    rw [actual_prepared map start offset len (offset.bytes+len.bytes) id first didSplit empty search split calculated]
    exact finish_data map offset.bytes (offset.bytes+len.bytes) map.size.bytes beginning _ final.1 final.2.2 final.2.1.1


/-- Slice-local ownership supplies all selected values of the actual iterator.
No ownership is demanded on disjoint original segments, and preparation success
is proved from well-formedness and bounds rather than supplied as a premise. -/
theorem selected_owned_on [DecidableEq α] (map : DedupRangeMap α) (offset len : Size)
    (well : map.WellFormed) (bounds : offset.bytes.toNat + len.bytes.toNat ≤ map.size.bytes.toNat)
    (predicate : α → Prop) (lower upper : UInt64) (owned : OwnedOn predicate lower upper map)
    (requestLower : lower.toNat ≤ offset.bytes.toNat)
    (requestUpper : (offset.bytes+len.bytes).toNat ≤ upper.toNat) :
    let result := map.iterMut offset len
    result.outcome = .ok () ∧ OwnedOn predicate lower upper result.state ∧
      ∀ cursor (valid : cursor < result.segments.size), predicate result.segments[cursor].data := by
  dsimp only
  have prepared := iter_mut map offset len well bounds
  let result := map.iterMut offset len
  have good : GeneralRangeMapPrepared.Good (fun _ => True) map.size.bytes result := prepared.1
  have selected : ∀ cursor (valid : cursor < result.segments.size),
      ∃ position, ∃ bounded : position < result.state.entries.size,
        result.segments[cursor] = result.state.entries[position] := by
    intro cursor valid
    have positionValid : cursor < result.positions.size := by rw [good.lengths];exact valid
    obtain ⟨bounded,same⟩ := good.selected cursor positionValid
    exact ⟨result.positions[cursor]'positionValid,bounded,same⟩
  have within : ∀ cursor (valid : cursor < result.segments.size),
      lower.toNat ≤ result.segments[cursor].range.start.toNat ∧
        result.segments[cursor].range.stop.toNat ≤ upper.toNat := by
    intro cursor valid
    have range := prepared.2.2 cursor valid
    exact ⟨Nat.le_trans requestLower range.1,Nat.le_trans range.2 requestUpper⟩
  exact ⟨good.outcome,refines_owned_on map result.state predicate lower upper good.wellFormed prepared.2.1 owned,
    GeneralRangeMapOrigins.selected_owned map result predicate lower upper good.wellFormed prepared.2.1 owned selected within⟩


end DuplicatePrefix.GeneralRangeMapOriginPrepare
#print axioms DuplicatePrefix.GeneralRangeMapOriginPrepare.iter_mut
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralRangeMapOriginPrepare." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual range preparation origin dependency {dependency}"
