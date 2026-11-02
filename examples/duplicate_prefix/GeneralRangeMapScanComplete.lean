import duplicate_prefix.GeneralRangeMapInvariant
namespace DuplicatePrefix.GeneralRangeMapScanComplete
open Miri Miri.ABI Miri.DataStructures
open DuplicatePrefix.GeneralRangeMapScanSafety GeneralRangeMapInvariant GeneralRangeMapState GeneralRangeMapGeometry GeneralRangeMapMerge
open DuplicatePrefix.GeneralRangeMapScan
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

theorem finishes [DecidableEq α] (predicate : α → Prop) (offset finish capacity : UInt64) (first : Nat)
    (inside : finish.toNat ≤ capacity.toNat) (initial : State α)
    (good : Good predicate offset finish capacity first initial) :
    let final := Lean.Loop.forIn (m := Id) {} initial (step finish)
    Good predicate offset finish capacity first final ∧ final.2.2.2.2.1 = true := by
  apply GeneralRangeMapFind.loop_finished (step finish) GeneralRangeMapScanSafety.measure
    (Good predicate offset finish capacity first)
    (fun state => Good predicate offset finish capacity first state ∧ state.2.2.2.2.1 = true)
    _ initial good
  intro state validState
  rcases state with ⟨map,equal,count,index,done,failure⟩
  have data := validState
  simp only [Good] at data
  rcases data with ⟨well,all,cap,failureEq,firstLE,equalLE,indexLE,firstValid,start,position⟩
  subst failure
  cases done with
  | true => exact .inl ⟨_,idle map equal count index finish,validState,rfl⟩
  | false =>
    simp only [Bool.false_eq_true,↓reduceIte] at position
    obtain ⟨current,startFinish⟩ := position
    have equalValid : equal < map.entries.size := by omega
    have insideMap : finish.toNat ≤ map.size.bytes.toNat := by rw [cap];exact inside
    have nextValid : map.entries[index].range.stop < finish → index+1 < map.entries.size :=
      next_valid map index current finish insideMap
    have alternatives :
        (count = 0 ∨ ∃ (before : map.entries[index].range.stop < finish) (eqValid : equal < map.entries.size),
          (map.entries[index+1]'(nextValid before)).data = map.entries[equal].data) ∨
        (0 < count ∧ (finish ≤ map.entries[index].range.stop ∨
          ∃ before : map.entries[index].range.stop < finish,
            (map.entries[index+1]'(nextValid before)).data ≠ map.entries[equal].data)) := by
      by_cases zero : count = 0
      · exact .inl (.inl zero)
      · have positive : 0 < count := by omega
        by_cases complete : finish ≤ map.entries[index].range.stop
        · exact .inr ⟨positive,.inl complete⟩
        · have before : map.entries[index].range.stop < finish := by
            apply UInt64.lt_iff_toNat_lt.mpr
            simp only [UInt64.le_iff_toNat_le] at complete
            omega
          by_cases same : (map.entries[index+1]'(nextValid before)).data = map.entries[equal].data
          · exact .inl (.inr ⟨before,equalValid,same⟩)
          · exact .inr ⟨positive,.inr ⟨before,same⟩⟩
    rcases alternatives with plain | ⟨positive,chosen⟩
    · let next : State α := (map,equal,count,index+1,decide (finish ≤ map.entries[index].range.stop),none)
      refine .inr ⟨next,advance_no_merge map equal count index finish current nextValid plain,?_,?_⟩
      · exact plain_good predicate offset finish capacity first map equal count index current validState inside
          equal count firstLE (by omega)
      · by_cases complete : finish ≤ map.entries[index].range.stop <;> simp [GeneralRangeMapScanSafety.measure,next,complete] <;> omega
    · by_cases same : equal = index
      · subst equal
        let next : State α := (map,index+1,count-1,index+1,decide (finish ≤ map.entries[index].range.stop),none)
        refine .inr ⟨next,advance_merge_single map count index finish current positive nextValid chosen,?_,?_⟩
        · exact plain_good predicate offset finish capacity first map index count index current validState inside
            (index+1) (count-1) (by omega) (by omega)
        · by_cases complete : finish ≤ map.entries[index].range.stop <;> simp [GeneralRangeMapScanSafety.measure,next,complete] <;> omega
      · have earlier : equal < index := by omega
        let next : State α := (mergeMap map equal (index+1) (by omega) (by omega),equal+1,count+(index-equal),equal+1,
          decide (finish ≤ map.entries[index].range.stop),none)
        refine .inr ⟨next,advance_merge_many map equal count index finish current positive earlier nextValid chosen,?_,?_⟩
        · exact merged_good predicate offset finish capacity first map equal count index current earlier validState inside
        · have resultSize : (mergeMap map equal (index+1) (by omega) (by omega)).entries.size =
              map.entries.size-(index-equal) := by rw [length];congr 1;omega
          by_cases complete : finish ≤ map.entries[index].range.stop <;>
            simp [GeneralRangeMapScanSafety.measure,next,complete,resultSize] <;> omega
end DuplicatePrefix.GeneralRangeMapScanComplete
