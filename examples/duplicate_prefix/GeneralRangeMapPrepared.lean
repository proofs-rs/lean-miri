import duplicate_prefix.GeneralRangeMapScanComplete
namespace DuplicatePrefix.GeneralRangeMapPrepared
open Miri Miri.ABI Miri.DataStructures
open DuplicatePrefix.RangeMapNonempty GeneralRangeMapScanSafety GeneralRangeMapState GeneralRangeMapGeometry
open DuplicatePrefix.GeneralRangeMapScan GeneralRangeMapPrepare
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

structure Good (predicate : α → Prop) (capacity : UInt64) (result : IterMutResult α) : Prop where
  outcome : result.outcome = .ok ()
  wellFormed : result.state.WellFormed
  every : Every predicate result.state
  capacity : result.state.size.bytes = capacity
  lengths : result.positions.size = result.segments.size
  selected : ∀ cursor (valid : cursor < result.positions.size),
    ∃ bounded : result.positions[cursor] < result.state.entries.size,
      result.segments[cursor]'(by rw [←lengths];exact valid) = result.state.entries[result.positions[cursor]]

theorem selected_exact (map : DedupRangeMap α) (first stop : Nat)
    (ordered : first ≤ stop) (bounded : stop ≤ map.entries.size) :
    range_selected_slice map.entries first stop = .ok (map.entries.extract first stop) := by
  have notReverse : ¬ stop < first := by omega
  have notPast : ¬ map.entries.size < stop := by omega
  simp_range_helpers
  simp [notReverse,notPast,pure,Except.pure]

theorem explicit_good (predicate : α → Prop) (capacity : UInt64) (map : DedupRangeMap α)
    (first stop : Nat) (ordered : first ≤ stop) (bounded : stop ≤ map.entries.size)
    (well : map.WellFormed) (all : Every predicate map) (cap : map.size.bytes = capacity) :
    Good predicate capacity ⟨map,(List.range (stop-first)).toArray.map (·+first),
      map.entries.extract first stop,.ok ()⟩ := by
  have lengths : ((List.range (stop-first)).toArray.map (·+first)).size = (map.entries.extract first stop).size := by
    simp only [Array.size_map,List.size_toArray,List.length_range,Array.size_extract]
    omega
  refine ⟨rfl,well,all,cap,lengths,?_⟩
  intro cursor valid
  have cursorValid : cursor < stop-first := by simpa using valid
  have position : ((List.range (stop-first)).toArray.map (·+first))[cursor]'valid = cursor+first := by simp
  refine ⟨by simp only [position];omega,?_⟩
  simp [position,Nat.add_comm]

theorem finish_good (predicate : α → Prop) (offset finish capacity : UInt64) (first : Nat)
    (state : State α) (good : GeneralRangeMapScanSafety.Good predicate offset finish capacity first state)
    (done : state.2.2.2.2.1 = true) (cloneData : α → α)
    (cloneGood : ∀ data, predicate data → predicate (cloneData data)) :
    Good predicate capacity (finishPrepared first finish cloneData state) := by
  rcases state with ⟨map,equal,count,index,active,failure⟩
  dsimp only at done
  subst active
  simp only [GeneralRangeMapScanSafety.Good,↓reduceIte] at good
  rcases good with ⟨well,all,cap,failureEq,firstLE,equalLE,indexLE,firstValid,start,lastValid,firstLT,startFinish,finishStop⟩
  subst failure
  obtain ⟨current,didSplit,split,currentWell,currentCap,currentAll,lastNew,stopFinish⟩ :=
    GeneralRangeMapSplit.prepare_end predicate map (index-1) lastValid finish cloneData well all cloneGood
      (UInt64.lt_iff_toNat_lt.mpr startFinish) (UInt64.le_iff_toNat_le.mpr finishStop)
  have positive : 0 < index := by omega
  have newBound : index ≤ current.entries.size := by omega
  have ordered : first ≤ index := by omega
  have sourceSelected := selected_exact current first index ordered newBound
  unfold finishPrepared
  simp only [Id.run,bind,pure]
  rw [split]
  dsimp only
  have indexEq : index-1+1 = index := by omega
  rw [indexEq,sourceSelected]
  exact explicit_good predicate capacity current first index ordered newBound currentWell currentAll (currentCap.trans cap)
end DuplicatePrefix.GeneralRangeMapPrepared
