import duplicate_prefix.GeneralRangeMapOriginPrepare
namespace DuplicatePrefix.GeneralRangeMapCoverage
open Miri Miri.ABI Miri.DataStructures
open DuplicatePrefix.RangeMapNonempty GeneralRangeMapState GeneralRangeMapGeometry GeneralRangeMapOrigins
open GeneralRangeMapScan GeneralRangeMapPrepare GeneralRangeMapOriginPrepare
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem finish_window (original : DedupRangeMap α) (offset finish capacity : UInt64) (first : Nat)
    (state : State α) (good : GeneralRangeMapScanSafety.Good (fun _ => True) offset finish capacity first state)
    (done : state.2.2.2.2.1 = true) (refined : Refines original state.1) :
    let result := finishPrepared first finish id state
    ∃ stop, first < stop ∧ stop ≤ result.state.entries.size ∧
      result.positions = (List.range (stop-first)).toArray.map (·+first) ∧
      (result.state.entries[first]?).map (·.range.start) = some offset ∧
      (result.state.entries[stop-1]?).map (·.range.stop) = some finish := by
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
  refine ⟨index,ordered,newBound,rfl,?_,?_⟩
  · simp only [Array.getElem?_eq_getElem (xs := current.entries) (i := first) (by omega),Option.map_some,currentStart]
  · simp only [Array.getElem?_eq_getElem (xs := current.entries) (i := index-1) (by omega),Option.map_some,stopFinish]

theorem iter_window [DecidableEq α] (map : DedupRangeMap α) (offset len : Size)
    (well : map.WellFormed) (bounds : offset.bytes.toNat + len.bytes.toNat ≤ map.size.bytes.toNat) :
    let result := map.iterMut offset len
    len.bytes = 0 ∨ ∃ first stop, first < stop ∧ stop ≤ result.state.entries.size ∧
      result.positions = (List.range (stop-first)).toArray.map (·+first) ∧
      (result.state.entries[first]?).map (·.range.start) = some offset.bytes ∧
      (result.state.entries[stop-1]?).map (·.range.stop) = some (offset.bytes+len.bytes) := by
  dsimp only
  unfold DedupRangeMap.iterMut
  by_cases empty : len.bytes = 0
  · have actual : map.iterMutWithClone offset len id = ⟨map,#[],#[],.ok ()⟩ := by
      simp [DedupRangeMap.iterMutWithClone,empty]
    rw [actual]
    exact Or.inl empty
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
    exact Or.inr ⟨beginning, finish_window map offset.bytes (offset.bytes+len.bytes) map.size.bytes beginning _ final.1 final.2.2 final.2.1.1⟩


/-- Every prepared segment overlapping a positive request is selected by the
actual iterator. The positivity assumption is necessary for empty requests. -/
theorem overlap_selected [DecidableEq α] (map : DedupRangeMap α) (offset len : Size)
    (well : map.WellFormed) (bounds : offset.bytes.toNat + len.bytes.toNat ≤ map.size.bytes.toNat)
    (positive : offset.bytes.toNat < (offset.bytes+len.bytes).toNat)
    (index : Nat) (valid : index < (map.iterMut offset len).state.entries.size)
    (afterStart : (map.iterMut offset len).state.entries[index].range.start.toNat < (offset.bytes+len.bytes).toNat)
    (beforeStop : offset.bytes.toNat < (map.iterMut offset len).state.entries[index].range.stop.toNat) :
    ∃ cursor, ∃ bounded : cursor < (map.iterMut offset len).positions.size,
      (map.iterMut offset len).positions[cursor] = index := by
  have prepared := GeneralRangeMapOriginPrepare.iter_mut map offset len well bounds
  obtain empty | ⟨first,stop,ordered,bounded,positions,start,finish⟩ := iter_window map offset len well bounds
  · simp only [empty,UInt64.add_zero] at positive
    omega
  · have startEq : ((map.iterMut offset len).state.entries[first]'(by omega)).range.start = offset.bytes := by
      simpa only [Array.getElem?_eq_getElem (xs := (map.iterMut offset len).state.entries) (i := first) (by omega),Option.map_some,Option.some.injEq] using start
    have finishEq : ((map.iterMut offset len).state.entries[stop-1]'(by omega)).range.stop = offset.bytes+len.bytes := by
      simpa only [Array.getElem?_eq_getElem (xs := (map.iterMut offset len).state.entries) (i := stop-1) (by omega),Option.map_some,Option.some.injEq] using finish
    have firstLE : first ≤ index := by
      by_cases possible : first ≤ index
      · exact possible
      have separated := stop_le_start (map.iterMut offset len).state prepared.1.wellFormed
        index first (by omega) (by omega)
      rw [startEq] at separated
      omega
    have indexLT : index < stop := by
      by_cases possible : index < stop
      · exact possible
      have separated := stop_le_start (map.iterMut offset len).state prepared.1.wellFormed
        (stop-1) index (by omega) valid
      rw [finishEq] at separated
      omega
    refine ⟨index-first,?_,?_⟩
    · rw [positions]
      simp only [Array.size_map,List.size_toArray,List.length_range]
      omega
    · simp only [positions,Array.getElem_map,List.getElem_toArray,List.getElem_range]
      omega

/-- Every requested byte belongs to a selected segment in the prepared map. -/
theorem point_selected [DecidableEq α] (map : DedupRangeMap α) (offset len : Size)
    (well : map.WellFormed) (bounds : offset.bytes.toNat + len.bytes.toNat ≤ map.size.bytes.toNat)
    (point : UInt64) (lower : offset.bytes.toNat ≤ point.toNat)
    (upper : point.toNat < (offset.bytes+len.bytes).toNat) :
    ∃ cursor, ∃ bounded : cursor < (map.iterMut offset len).positions.size,
      Contains (map.iterMut offset len).state point ((map.iterMut offset len).positions[cursor]) := by
  have fits : offset.bytes.toNat+len.bytes.toNat < 2^64 := Nat.lt_of_le_of_lt bounds map.size.bytes.toNat_lt
  have finishNat : (offset.bytes+len.bytes).toNat = offset.bytes.toNat+len.bytes.toNat := by
    simp only [UInt64.toNat_add,Nat.mod_eq_of_lt fits]
  have prepared := GeneralRangeMapOriginPrepare.iter_mut map offset len well bounds
  have capacity := congrArg UInt64.toNat prepared.1.capacity
  obtain ⟨index,valid,afterStart,beforeStop⟩ := covered (map.iterMut offset len).state prepared.1.wellFormed point (by omega)
  obtain ⟨cursor,bounded,same⟩ := overlap_selected map offset len well bounds (by omega) index valid (by omega) (by omega)
  refine ⟨cursor,bounded,?_⟩
  rw [same]
  exact ⟨valid,afterStart,beforeStop⟩

end DuplicatePrefix.GeneralRangeMapCoverage
