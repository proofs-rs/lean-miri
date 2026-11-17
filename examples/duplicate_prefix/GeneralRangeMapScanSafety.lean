import duplicate_prefix.GeneralRangeMapPrepare
import duplicate_prefix.GeneralRangeMapFind
namespace DuplicatePrefix.GeneralRangeMapScanSafety
open Miri Miri.ABI Miri.DataStructures
open DuplicatePrefix.RangeMapNonempty GeneralRangeMapState GeneralRangeMapGeometry GeneralRangeMapMerge
open DuplicatePrefix.GeneralRangeMapScan
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def Good (predicate : α → Prop) (offset finish capacity : UInt64) (first : Nat) (state : State α) : Prop :=
  let map := state.1
  let equalSince := state.2.1
  let index := state.2.2.2.1
  map.WellFormed ∧ Every predicate map ∧ map.size.bytes = capacity ∧
  state.2.2.2.2.2 = none ∧ first ≤ equalSince ∧ equalSince ≤ index ∧ index ≤ map.entries.size ∧
  ∃ initial : first < map.entries.size,
    map.entries[first].range.start = offset ∧
    if state.2.2.2.2.1 then
      ∃ previous : index-1 < map.entries.size, first < index ∧
        map.entries[index-1].range.start.toNat < finish.toNat ∧
        finish.toNat ≤ map.entries[index-1].range.stop.toNat
    else ∃ current : index < map.entries.size, map.entries[index].range.start.toNat < finish.toNat

def measure (state : State α) : Nat :=
  if state.2.2.2.2.1 then 0 else state.1.entries.size-state.2.2.2.1+1

theorem idle [DecidableEq α] (map : DedupRangeMap α) (equal count index : Nat) (finish : UInt64) :
    step finish () (map,equal,count,index,true,none) = .done (map,equal,count,index,true,none) := by
  simp [step,pure]

theorem advance_no_merge [DecidableEq α] (map : DedupRangeMap α) (equal count index : Nat)
    (finish : UInt64) (valid : index < map.entries.size)
    (nextValid : map.entries[index].range.stop < finish → index+1 < map.entries.size)
    (plain : count = 0 ∨ (∃ (before : map.entries[index].range.stop < finish) (equalValid : equal < map.entries.size),
        (map.entries[index+1]'(nextValid before)).data = map.entries[equal].data)) :
    step finish () (map,equal,count,index,false,none) =
      .yield (map,equal,count,index+1,decide (finish ≤ map.entries[index].range.stop),none) := by
  unfold step
  simp_range_helpers
  simp only [Bool.not_false,Bool.true_and,Option.isNone_none,Bool.and_self,↓reduceIte,valid,
    Array.getElem?_eq_getElem valid]
  by_cases complete : finish ≤ map.entries[index].range.stop
  · rcases plain with zero | ⟨before,rest⟩
    · simp [complete,zero,pure]
    · exact False.elim (by
        have c := UInt64.le_iff_toNat_le.mp complete
        have b := UInt64.lt_iff_toNat_lt.mp before
        omega)
  · have before : map.entries[index].range.stop < finish := by
      apply UInt64.lt_iff_toNat_lt.mpr
      simp only [UInt64.le_iff_toNat_le] at complete
      omega
    have next := nextValid before
    have notPast : ¬ map.entries.size ≤ index+1 := by omega
    rcases plain with zero | ⟨_,eqValid,equalData⟩
    · simp [complete,zero,next,notPast,pure]
    · simp [complete,next,eqValid,equalData,notPast,pure]

theorem advance_merge_single [DecidableEq α] (map : DedupRangeMap α) (count index : Nat)
    (finish : UInt64) (valid : index < map.entries.size) (positive : 0 < count)
    (nextValid : map.entries[index].range.stop < finish → index+1 < map.entries.size)
    (chosen : finish ≤ map.entries[index].range.stop ∨
      ∃ before : map.entries[index].range.stop < finish,
        (map.entries[index+1]'(nextValid before)).data ≠ map.entries[index].data) :
    step finish () (map,index,count,index,false,none) =
      .yield (map,index+1,count-1,index+1,decide (finish ≤ map.entries[index].range.stop),none) := by
  unfold step
  simp_range_helpers
  simp only [Bool.not_false,Option.isNone_none,Bool.and_self,↓reduceIte,valid]
  by_cases complete : finish ≤ map.entries[index].range.stop
  · simp [complete,positive]
  · have before : map.entries[index].range.stop < finish := by
      apply UInt64.lt_iff_toNat_lt.mpr
      simp only [UInt64.le_iff_toNat_le] at complete
      omega
    have next := nextValid before
    have notPast : ¬ map.entries.size ≤ index+1 := by omega
    have different : (map.entries[index+1]'next).data ≠ map.entries[index].data := by
      rcases chosen with finished | ⟨_,different⟩
      · exact False.elim (complete finished)
      · exact different
    simp [complete,next,notPast,different,positive]

theorem advance_merge_many [DecidableEq α] (map : DedupRangeMap α) (equal count index : Nat)
    (finish : UInt64) (valid : index < map.entries.size) (positive : 0 < count) (earlier : equal < index)
    (nextValid : map.entries[index].range.stop < finish → index+1 < map.entries.size)
    (chosen : finish ≤ map.entries[index].range.stop ∨
      ∃ before : map.entries[index].range.stop < finish,
        (map.entries[index+1]'(nextValid before)).data ≠ (map.entries[equal]'(by omega)).data) :
    step finish () (map,equal,count,index,false,none) =
      .yield (mergeMap map equal (index+1) (by omega) (by omega),equal+1,count+(index-equal),equal+1,
        decide (finish ≤ map.entries[index].range.stop),none) := by
  have equalValid : equal < map.entries.size := by omega
  have removedPositive : 0 < index+1-equal-1 := by omega
  have indexEq : index+1-(index+1-equal-1) = equal+1 := by omega
  have removedEq : index+1-equal-1 = index-equal := by omega
  have indexEq2 : index+1-(index-equal) = equal+1 := by omega
  unfold step
  simp_range_helpers
  simp only [Bool.not_false,Option.isNone_none,Bool.and_self,↓reduceIte,valid]
  by_cases complete : finish ≤ map.entries[index].range.stop
  · simp only [complete,decide_true, Bool.not_true,Bool.false_and,↓reduceIte,positive,removedPositive]
    rw [actual map equal (index+1) (by omega) (by omega)]
    have notBefore : ¬ map.entries[index].range.stop < finish := by
      simp only [UInt64.lt_iff_toNat_lt,UInt64.le_iff_toNat_le] at *
      omega
    simp [complete,notBefore,indexEq2,removedEq]
  · have before : map.entries[index].range.stop < finish := by
      apply UInt64.lt_iff_toNat_lt.mpr
      simp only [UInt64.le_iff_toNat_le] at complete
      omega
    have next := nextValid before
    have notPast : ¬ map.entries.size ≤ index+1 := by omega
    have different : (map.entries[index+1]'next).data ≠ map.entries[equal].data := by
      rcases chosen with finished | ⟨_,different⟩
      · exact False.elim (complete finished)
      · exact different
    simp only [complete,decide_false,Bool.not_false,Bool.true_and,notPast,↓reduceIte,positive,
      next,equalValid,bne_iff_ne,different,removedPositive]
    rw [actual map equal (index+1) (by omega) (by omega)]
    simp [complete,before,next,notPast,equalValid,different,indexEq2,removedEq]
end DuplicatePrefix.GeneralRangeMapScanSafety
