import duplicate_prefix.GeneralBorrowFreshMutableGeometry
import duplicate_prefix.GeneralBorrowProtectedReadableStage
import duplicate_prefix.GeneralBorrowProtectedReadRangeExposureCache
import duplicate_prefix.GeneralBorrowProtectedConstructorExposureCache
namespace DuplicatePrefix.GeneralBorrowTwoProtectedCacheReadyStage
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapState GeneralBorrowExposureCardinality
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem cache (input : GeneralBorrowFreshMetadataChildMutable.Input) (protections : ProtectedTags)
    (roots : input.tree.roots = #[input.parent])
    (profile : Every (GeneralBorrowProtectedReadRelease.Profile input.tree protections) input.tree.locations)
    (initial : Every (fun location => LocationCoherent input.tree location protections) input.tree.locations)
    (prepared : GeneralBorrowProtectedReadableStage.Prepared input protections) :
    Every (fun location => LocationCoherent (GeneralBorrowProtectedReadableStage.child input protections).tree location protections)
      (GeneralBorrowProtectedReadableStage.child input protections).tree.locations := by
  have read := GeneralBorrowProtectedReadRangeExposureCache.ranged input.tree protections input.parentTag input.parent input.parent
    (Size.ofBytes input.offset) (Size.ofBytes input.len) .VisitChildrenOfAccessed input.depth input.children input.parentNode input.parentPresent
    roots input.covered input.parentTagPresent input.well initial input.offset (input.offset+input.len)
    (by intro position valid positive low high;exact profile position valid) (Nat.le_refl _) (Nat.le_refl _) input.bounds
  have readCache : Every (fun location => LocationCoherent prepared.next.tree location protections) prepared.next.tree.locations := by
    rw [prepared.tree]
    exact read.2.1
  have constructed := (GeneralBorrowProtectedConstructorExposureCache.append prepared.next protections readCache).2
  rw [prepared.result] at constructed
  exact constructed
theorem geometry (input : GeneralBorrowFreshMetadataChildMutable.Input) (protections : ProtectedTags)
    (roots : input.tree.roots = #[input.parent])
    (profile : Every (GeneralBorrowProtectedReadRelease.Profile input.tree protections) input.tree.locations)
    (initial : Every (fun location => LocationCoherent input.tree location protections) input.tree.locations)
    (prepared : GeneralBorrowProtectedReadableStage.Prepared input protections) :
    (GeneralBorrowProtectedReadableStage.child input protections).tree.locations.WellFormed ∧
      (GeneralBorrowProtectedReadableStage.child input protections).tree.locations.size = input.tree.locations.size := by
  have read := GeneralBorrowProtectedReadRangeExposureCache.ranged input.tree protections input.parentTag input.parent input.parent
    (Size.ofBytes input.offset) (Size.ofBytes input.len) .VisitChildrenOfAccessed input.depth input.children input.parentNode input.parentPresent
    roots input.covered input.parentTagPresent input.well initial input.offset (input.offset+input.len)
    (by intro position valid positive low high;exact profile position valid) (Nat.le_refl _) (Nat.le_refl _) input.bounds
  have constructed := GeneralBorrowFreshMutableGeometry.append_frame prepared.next
  have capacity : prepared.next.tree.locations.size = input.tree.locations.size := by
    rw [prepared.tree]
    exact read.2.2.2.1
  rw [prepared.result] at constructed
  exact ⟨constructed.1,constructed.2.trans capacity⟩

end DuplicatePrefix.GeneralBorrowTwoProtectedCacheReadyStage
