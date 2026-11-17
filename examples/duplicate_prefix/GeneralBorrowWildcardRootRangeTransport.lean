import duplicate_prefix.GeneralBorrowWildcardRootCache
import duplicate_prefix.GeneralBorrowFreshInstallation
namespace DuplicatePrefix.GeneralBorrowWildcardRootRangeTransport
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- Real selected range insertion transports any current row predicate through
its literal materialization, including split boundaries and repeated updates. -/
theorem transport (map : DedupRangeMap LocationTree) (index : UniIndex) (state : LocationState)
    (offset len : Size) (well : map.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ map.size.bytes.toNat)
    (P Q : LocationTree → Prop)
    (owned : OwnedOn P offset.bytes (offset.bytes+len.bytes) map)
    (step : ∀ location,P location → Q {location with perms := location.perms.insert index state}) :
    OwnedOn Q offset.bytes (offset.bytes+len.bytes)
      (map.modifyRange offset len (fun _ location => {location with perms := location.perms.insert index state})).state := by
  let modify : ByteRange → LocationTree → LocationTree := fun _ location => {location with perms := location.perms.insert index state}
  let changed := map.modifyRange offset len modify
  let prepared := map.iterMut offset len
  have idempotent : ∀ range value,modify range (modify range value) = modify range value := by
    intro range value
    simp only [modify,GeneralBorrowFreshInstallation.insert_idempotent]
  have sizes : changed.state.entries.size = prepared.state.entries.size := by
    rw [GeneralBorrowFreshModify.state_exact map offset len modify well bounds,GeneralBorrowFreshModify.fold_size]
  intro position valid positive start stop
  have oldValid : position < prepared.state.entries.size := by rw [←sizes];exact valid
  obtain ⟨outputValid,entryEq⟩ := GeneralBorrowFreshModify.entry_exact map offset len modify idempotent well bounds position oldValid
  have rangeEq : (changed.state.entries[position]'valid).range = (prepared.state.entries[position]'oldValid).range := by
    have known := congrArg RangeMapSegment.range entryEq
    split at known <;> exact known
  change (changed.state.entries[position]'valid).range.start.toNat < (offset.bytes+len.bytes).toNat at start
  change offset.bytes.toNat < (changed.state.entries[position]'valid).range.stop.toNat at stop
  rw [rangeEq] at start stop
  obtain ⟨cursor,bounded,same⟩ := GeneralRangeMapCoverage.overlap_selected map offset len well bounds positive position oldValid start stop
  have member : position ∈ prepared.positions.toList := by
    apply Array.mem_def.mp
    exact Array.mem_iff_getElem.mpr ⟨cursor,bounded,same⟩
  change position ∈ (map.iterMut offset len).positions.toList at member
  simp only [member,↓reduceIte] at entryEq
  have before := (GeneralRangeMapOriginPrepare.selected_owned_on map offset len well bounds
    P offset.bytes (offset.bytes+len.bytes) owned (Nat.le_refl _) (Nat.le_refl _)).2.1
      position oldValid positive start stop
  change Q (changed.state.entries[position]'valid).data
  rw [entryEq]
  exact step _ before
end DuplicatePrefix.GeneralBorrowWildcardRootRangeTransport
