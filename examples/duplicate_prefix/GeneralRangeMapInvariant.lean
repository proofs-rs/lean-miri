import duplicate_prefix.GeneralRangeMapScanSafety
namespace DuplicatePrefix.GeneralRangeMapInvariant
open Miri Miri.ABI Miri.DataStructures
open DuplicatePrefix.GeneralRangeMapScanSafety GeneralRangeMapState GeneralRangeMapGeometry GeneralRangeMapMerge
open DuplicatePrefix.GeneralRangeMapScan
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

theorem next_valid (map : DedupRangeMap α) (index : Nat) (valid : index < map.entries.size)
    (finish : UInt64) (inside : finish.toNat ≤ map.size.bytes.toNat)
    (before : map.entries[index].range.stop < finish) : index+1 < map.entries.size := by
  have last := size_last map (by omega)
  by_cases outside : index+1 < map.entries.size
  · exact outside
  · exfalso
    have indexLast : index = map.entries.size-1 := by omega
    have terminal : map.entries[index].range.stop = map.size.bytes := by simpa only [←indexLast] using last.symm
    have earlier := UInt64.lt_iff_toNat_lt.mp before
    rw [terminal] at earlier
    omega

theorem plain_good (predicate : α → Prop) (offset finish capacity : UInt64) (first : Nat)
    (map : DedupRangeMap α) (equal count index : Nat) (valid : index < map.entries.size)
    (good : Good predicate offset finish capacity first (map,equal,count,index,false,none))
    (inside : finish.toNat ≤ capacity.toNat)
    (nextEqual nextCount : Nat) (lower : first ≤ nextEqual) (upper : nextEqual ≤ index+1) :
    Good predicate offset finish capacity first
      (map,nextEqual,nextCount,index+1,decide (finish ≤ map.entries[index].range.stop),none) := by
  simp only [Good,Bool.false_eq_true,↓reduceIte] at good
  rcases good with ⟨well,all,cap,failure,firstLE,equalLE,indexLE,firstValid,start,current,startFinish⟩
  have bounded : index+1 ≤ map.entries.size := by omega
  refine ⟨well,all,cap,rfl,lower,upper,bounded,firstValid,start,?_⟩
  by_cases complete : finish ≤ map.entries[index].range.stop
  · simp only [complete,decide_true,↓reduceIte]
    refine ⟨by omega,by omega,?_,?_⟩
    · simpa only [Nat.add_sub_cancel] using startFinish
    · simpa only [Nat.add_sub_cancel] using UInt64.le_iff_toNat_le.mp complete
  · have before : map.entries[index].range.stop < finish := by
      apply UInt64.lt_iff_toNat_lt.mpr
      simp only [UInt64.le_iff_toNat_le] at complete
      omega
    have insideMap : finish.toNat ≤ map.size.bytes.toNat := by rw [cap];exact inside
    have next := next_valid map index current finish insideMap before
    simp only [complete,decide_false,Bool.false_eq_true,↓reduceIte]
    refine ⟨next,?_⟩
    have adjacent := (facts map well (by omega)).2.2 index next
    have earlier := UInt64.lt_iff_toNat_lt.mp before
    omega

theorem merged_good (predicate : α → Prop) (offset finish capacity : UInt64) (first : Nat)
    (map : DedupRangeMap α) (equal count index : Nat) (valid : index < map.entries.size)
    (earlier : equal < index)
    (good : Good predicate offset finish capacity first (map,equal,count,index,false,none))
    (inside : finish.toNat ≤ capacity.toNat) :
    Good predicate offset finish capacity first
      (mergeMap map equal (index+1) (by omega) (by omega),equal+1,count+(index-equal),equal+1,
        decide (finish ≤ map.entries[index].range.stop),none) := by
  simp only [Good,Bool.false_eq_true,↓reduceIte] at good
  rcases good with ⟨well,all,cap,failure,firstLE,equalLE,indexLE,firstValid,start,current,startFinish⟩
  let result := mergeMap map equal (index+1) (by omega) (by omega)
  have resultSize : result.entries.size = map.entries.size-(index-equal) := by
    dsimp only [result]
    rw [length]
    congr 1
    omega
  have equalValid : equal < map.entries.size := by omega
  have newFirstValid : first < result.entries.size := by rw [resultSize];omega
  have resultWell : result.WellFormed := wellFormed map equal (index+1) (by omega) (by omega) well
  have resultAll : Every predicate result := every predicate map equal (index+1) (by omega) (by omega) all
  have resultCapacity : result.size.bytes = capacity := (size_bytes map equal (index+1) (by omega) (by omega)).trans cap
  have firstStart : result.entries[first].range.start = offset := by
    rw [start_left map equal (index+1) (by omega) (by omega) first firstLE]
    exact start
  have nextLE : equal+1 ≤ result.entries.size := by rw [resultSize];omega
  change Good predicate offset finish capacity first (result,equal+1,count+(index-equal),equal+1,_,none)
  dsimp only [Good]
  refine ⟨resultWell,resultAll,resultCapacity,rfl,by omega,by omega,nextLE,newFirstValid,firstStart,?_⟩
  have mergedStart : (result.entries[equal]'(by rw [resultSize];omega)).range.start = map.entries[equal].range.start :=
    start_left map equal (index+1) (by omega) (by omega) equal (by omega)
  have mergedStop : (result.entries[equal]'(by rw [resultSize];omega)).range.stop = map.entries[index].range.stop := by
    simpa only [Nat.add_sub_cancel] using stop_first map equal (index+1) (by omega) (by omega)
  by_cases complete : finish ≤ map.entries[index].range.stop
  · simp only [complete,decide_true,↓reduceIte]
    refine ⟨by omega,by omega,?_,?_⟩
    · simp only [Nat.add_sub_cancel]
      rw [mergedStart]
      have between := stop_le_start map well equal index earlier current
      have positive := (facts map well (by omega)).2.1 equal equalValid
      omega
    · simpa only [Nat.add_sub_cancel,mergedStop] using UInt64.le_iff_toNat_le.mp complete
  · have before : map.entries[index].range.stop < finish := by
      apply UInt64.lt_iff_toNat_lt.mpr
      simp only [UInt64.le_iff_toNat_le] at complete
      omega
    have insideMap : finish.toNat ≤ map.size.bytes.toNat := by rw [cap];exact inside
    have next := next_valid map index current finish insideMap before
    have nextNew : equal+1 < result.entries.size := by rw [resultSize];omega
    simp only [complete,decide_false,Bool.false_eq_true,↓reduceIte]
    refine ⟨nextNew,?_⟩
    have adjacent := (facts result resultWell (by omega)).2.2 equal nextNew
    have earlier := UInt64.lt_iff_toNat_lt.mp before
    rw [mergedStop] at adjacent
    omega
end DuplicatePrefix.GeneralRangeMapInvariant
