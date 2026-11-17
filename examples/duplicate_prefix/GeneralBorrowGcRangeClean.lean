import duplicate_prefix.GeneralBorrowGcVacantClean
import duplicate_prefix.GeneralBorrowTrimLookup
import duplicate_prefix.GeneralRangeMapThoroughEvery
namespace DuplicatePrefix.GeneralBorrowGcRangeClean
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open DuplicatePrefix.GeneralBorrowGcVacantClean DuplicatePrefix.GeneralBorrowFreshFutureClean DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

open Lean Elab Term in
elab "gc_source_trim_location" : term => do
  let found := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".BorrowTree.trimLocationForRangeEquality" then some name else none
  match found with
  | [name] => return mkConst name
  | _ => throwError "expected pinned location equality normalization"

/-- Actual GC equality normalization preserves every permission lookup. -/
theorem trim_location_get (location : LocationTree) (query : UniIndex) :
    (gc_source_trim_location location).perms.get query = location.perms.get query := by
  change location.perms.trimTrailingNone.get query = location.perms.get query
  exact GeneralBorrowTrimLookup.trim_get location.perms query

/-- Exposure-cache lookup semantics also survive the same normalization. -/
theorem trim_location_cache (location : LocationTree) (query : UniIndex) :
    (gc_source_trim_location location).exposedCache.nodes.get query = location.exposedCache.nodes.get query := by
  change location.exposedCache.nodes.trimTrailingNone.get query = location.exposedCache.nodes.get query
  exact GeneralBorrowTrimLookup.trim_get location.exposedCache.nodes query

/-- Allocation-wide GC location normalization preserves all vacant permissions. -/
theorem trim_preserves (tree : BorrowTree) (good : VacantClean tree) :
    VacantClean {tree with locations := tree.locations.modifyAll (fun _ location => gc_source_trim_location location)} := by
  intro query vacant position valid
  have previous : position < tree.locations.entries.size := by
    simpa only [DedupRangeMap.modifyAll,Array.size_map] using valid
  have clean := good query vacant position previous
  simpa only [DedupRangeMap.modifyAll,Array.getElem_map,trim_location_get] using clean

/-- Adjacent merging retains the vacant-slot invariant even on an error prefix.
This data statement does not classify an erroneous GC operation as safe. -/
theorem merge_preserves (tree : BorrowTree) (good : VacantClean tree) :
    VacantClean {tree with locations := tree.locations.mergeAdjacentThorough.state} := by
  intro query vacant
  exact GeneralRangeMapThoroughEvery.preserves (fun location : LocationTree => location.perms.get query = none)
    tree.locations (good query vacant)

/-- The exact two production postprocessing stages retain the invariant. -/
theorem finish_preserves (tree : BorrowTree) (good : VacantClean tree) :
    let normalized := {tree with locations := tree.locations.modifyAll (fun _ location => gc_source_trim_location location)}
    VacantClean {normalized with locations := normalized.locations.mergeAdjacentThorough.state} :=
  merge_preserves _ (trim_preserves tree good)
end DuplicatePrefix.GeneralBorrowGcRangeClean
