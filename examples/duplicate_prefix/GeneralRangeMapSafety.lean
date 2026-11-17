import duplicate_prefix.GeneralRangeMapPrepared
namespace DuplicatePrefix.GeneralRangeMapSafety
open Miri Miri.ABI Miri.DataStructures
open DuplicatePrefix.RangeMapNonempty GeneralRangeMapState GeneralRangeMapGeometry GeneralRangeMapPrepare
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

theorem iter_mut_with_clone [DecidableEq α] (predicate : α → Prop) (map : DedupRangeMap α)
    (offset len : Size) (cloneData : α → α) (well : map.WellFormed) (all : Every predicate map)
    (cloneGood : ∀ data, predicate data → predicate (cloneData data))
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ map.size.bytes.toNat) :
    GeneralRangeMapPrepared.Good predicate map.size.bytes (map.iterMutWithClone offset len cloneData) := by
  by_cases empty : len.bytes = 0
  · have actual : map.iterMutWithClone offset len cloneData = ⟨map,#[],#[],.ok ()⟩ := by
      simp [DedupRangeMap.iterMutWithClone,empty]
    rw [actual]
    refine ⟨rfl,well,all,rfl,rfl,?_⟩
    intro cursor valid
    simp at valid
  · have positive : 0 < len.bytes.toNat := by
      have unequal : len.bytes.toNat ≠ 0 := by
        intro zero
        exact empty (UInt64.toNat_inj.mp zero)
      omega
    have inside : offset.bytes.toNat < map.size.bytes.toNat := by omega
    have fits : offset.bytes.toNat + len.bytes.toNat < 2^64 :=
      Nat.lt_of_le_of_lt bounds map.size.bytes.toNat_lt
    have finishNat : (offset.bytes+len.bytes).toNat = offset.bytes.toNat+len.bytes.toNat := by
      simp only [UInt64.toNat_add,Nat.mod_eq_of_lt fits]
    have calculated := checked_end_add offset.bytes len.bytes fits
    obtain ⟨first,search,firstValid,afterStart,beforeEnd⟩ :=
      GeneralRangeMapFind.find_success map offset.bytes well inside
    obtain ⟨start,didSplit,split,startWell,startCap,startAll,startValid,startAt,startStop⟩ :=
      GeneralRangeMapSplit.prepare_start predicate map first firstValid offset.bytes cloneData well all cloneGood
        (UInt64.le_iff_toNat_le.mpr afterStart) (UInt64.lt_iff_toNat_lt.mpr beforeEnd)
    let beginning := if didSplit then first+1 else first
    have beginValid : beginning < start.entries.size := by
      cases didSplit <;> simpa [beginning] using startValid
    have beginAt : (start.entries[beginning]'beginValid).range.start = offset.bytes := by
      cases didSplit <;> simpa [beginning] using startAt
    let initial : GeneralRangeMapScan.State α := (start,beginning,3,beginning,false,none)
    have initialGood : GeneralRangeMapScanSafety.Good predicate offset.bytes (offset.bytes+len.bytes)
        map.size.bytes beginning initial := by
      dsimp only [GeneralRangeMapScanSafety.Good,initial]
      refine ⟨startWell,startAll,startCap,rfl,by omega,by omega,by omega,beginValid,beginAt,?_⟩
      simp only [Bool.false_eq_true,↓reduceIte]
      refine ⟨beginValid,?_⟩
      rw [beginAt,finishNat]
      omega
    have finishInside : (offset.bytes+len.bytes).toNat ≤ map.size.bytes.toNat := by rw [finishNat];exact bounds
    have loopGood := GeneralRangeMapScanComplete.finishes predicate offset.bytes (offset.bytes+len.bytes)
      map.size.bytes beginning finishInside initial initialGood
    rw [actual_prepared map start offset len (offset.bytes+len.bytes) cloneData first didSplit empty search split calculated]
    exact GeneralRangeMapPrepared.finish_good predicate offset.bytes (offset.bytes+len.bytes) map.size.bytes beginning
      _ loopGood.1 loopGood.2 cloneData cloneGood

theorem iter_mut [DecidableEq α] (predicate : α → Prop) (map : DedupRangeMap α)
    (offset len : Size) (well : map.WellFormed) (all : Every predicate map)
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ map.size.bytes.toNat) :
    GeneralRangeMapPrepared.Good predicate map.size.bytes (map.iterMut offset len) := by
  exact iter_mut_with_clone predicate map offset len id well all (fun _ good => good) bounds

end DuplicatePrefix.GeneralRangeMapSafety
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralRangeMapSafety." then
      for dependency in (←collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved arbitrary range iterator dependency {dependency}"
