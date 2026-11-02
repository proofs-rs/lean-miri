import duplicate_prefix.GeneralBorrowFreshModify
import duplicate_prefix.GeneralRangeMapOriginPrepare
import duplicate_prefix.GeneralBorrowSifaCacheFrame

namespace DuplicatePrefix.GeneralBorrowFreshCacheWitness
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- A resulting location retains the cache of some initial raw-data witness.
The witness may contain graph/permission records and is not an outcome premise. -/
def Witness (predicate : LocationTree → Prop) (location : LocationTree) : Prop :=
  ∃ original, predicate original ∧ location.exposedCache = original.exposedCache

/-- Any actual idempotent permission-only range callback retains a data-bearing
cache origin throughout the caller's slice, including prepared but unmodified
segments. Preparation and mutation outcomes are derived internally. -/
theorem modified (map : DedupRangeMap LocationTree) (offset len : Size)
    (modify : ByteRange → LocationTree → LocationTree)
    (idempotent : ∀ range location, modify range (modify range location) = modify range location)
    (cacheFrame : ∀ range location, (modify range location).exposedCache = location.exposedCache)
    (well : map.WellFormed) (bounds : offset.bytes.toNat+len.bytes.toNat ≤ map.size.bytes.toNat)
    (predicate : LocationTree → Prop) (lower upper : UInt64)
    (owned : OwnedOn predicate lower upper map)
    (requestLower : lower.toNat ≤ offset.bytes.toNat) (requestUpper : (offset.bytes+len.bytes).toNat ≤ upper.toNat) :
    OwnedOn (Witness predicate) lower upper (map.modifyRange offset len modify).state := by
  let prepared := map.iterMut offset len
  let modified := map.modifyRange offset len modify
  have preparedOwners := GeneralRangeMapOriginPrepare.selected_owned_on map offset len well bounds predicate lower upper owned requestLower requestUpper
  have sizeEq : modified.state.entries.size = prepared.state.entries.size := by
    rw [GeneralBorrowFreshModify.state_exact map offset len modify well bounds,GeneralBorrowFreshModify.fold_size]
  intro position valid positive beforeUpper afterLower
  have oldValid : position < prepared.state.entries.size := by rw [←sizeEq];exact valid
  obtain ⟨outputValid,outputEq⟩ := GeneralBorrowFreshModify.entry_exact map offset len modify idempotent well bounds position oldValid
  have cacheEq : (modified.state.entries[position]'valid).data.exposedCache =
      (prepared.state.entries[position]'oldValid).data.exposedCache := by
    rw [outputEq]
    split
    · exact cacheFrame _ _
    · rfl
  have rangeEq : (modified.state.entries[position]'valid).range =
      (prepared.state.entries[position]'oldValid).range := by
    rw [outputEq]
    split <;> rfl
  rw [rangeEq] at beforeUpper afterLower
  exact ⟨_,preparedOwners.2.1 position oldValid positive beforeUpper afterLower,cacheEq⟩

/-- Actual SIFA processing keeps same-position cache witnesses even when it
changes stored permission SIFA or default node SIFA. Its real cacheShape frame
retains all range boundaries, without any successful-operation hypothesis. -/
theorem shape_preserves (before after : BorrowTree)
    (same : GeneralBorrowSifaCacheFrame.cacheShape after = GeneralBorrowSifaCacheFrame.cacheShape before)
    (predicate : LocationTree → Prop) (lower upper : UInt64)
    (owned : OwnedOn (Witness predicate) lower upper before.locations) :
    OwnedOn (Witness predicate) lower upper after.locations := by
  have sizes : after.locations.entries.size = before.locations.entries.size := by
    have known := congrArg Array.size same
    simpa only [GeneralBorrowSifaCacheFrame.cacheShape,Array.size_map] using known
  intro position valid positive beforeUpper afterLower
  have oldValid : position < before.locations.entries.size := by rw [←sizes];exact valid
  have pairEq : ((after.locations.entries[position]'valid).range,(after.locations.entries[position]'valid).data.exposedCache) =
      ((before.locations.entries[position]'oldValid).range,(before.locations.entries[position]'oldValid).data.exposedCache) := by
    have selected := congrArg (fun rows => rows[position]?) same
    simp only [GeneralBorrowSifaCacheFrame.cacheShape,Array.getElem?_map,Array.getElem?_eq_getElem valid,
      Array.getElem?_eq_getElem oldValid,Option.map_some] at selected
    exact Option.some.inj selected
  have fields := Prod.mk.inj pairEq
  rw [fields.1] at beforeUpper afterLower
  obtain ⟨original,data,cacheEq⟩ := owned position oldValid positive beforeUpper afterLower
  exact ⟨original,data,fields.2.trans cacheEq⟩

end DuplicatePrefix.GeneralBorrowFreshCacheWitness
