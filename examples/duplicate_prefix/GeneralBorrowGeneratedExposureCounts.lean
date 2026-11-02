import duplicate_prefix.GeneralBorrowGeneratedExposureReady
import duplicate_prefix.GeneralBorrowStarExposureCounts
namespace DuplicatePrefix.GeneralBorrowGeneratedExposureCounts
open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshMetadataChildShared DuplicatePrefix.GeneralBorrowFullSharedStep
open DuplicatePrefix.GeneralBorrowGeneratedStarShape DuplicatePrefix.GeneralBorrowExposeReadFold
open DuplicatePrefix.GeneralBorrowStarExposureCounts
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- Actual allocation, positive full-slice Read/shared generation, then exposure
of every generated child. All requests, node flags and cache data are derived.
The explicit history budget bounds actual UInt16 counters within Lean alone.
This protocol does not yet include arbitrary mixed histories or GC. -/
theorem generate (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag childTag : BorTag)
    (different : rootTag ≠ childTag) (tags : List BorTag) (distinct : tags.Nodup)
    (rootUnused : rootTag ∉ tags) (childUnused : childTag ∉ tags)
    (short : 1+tags.length < 65536) (protections : ProtectedTags) :
    let seed := GeneralBorrowFullSharedSeed.input capacity nonzero rootTag childTag different
    ∃ final finalLocation requests exposedLocation,
      GeneralBorrowFullSharedRepeat.Run seed tags final ∧ State final finalLocation ∧
      requests.map Request.leaf = final.parentNode.children.toList ∧
      (run protections requests final.tree).outcome = .ok () ∧
      (run protections requests final.tree).tree.locations =
        RangeMapNonempty.homogeneous capacity exposedLocation ∧
      Counts exposedLocation.exposedCache final.parent (requests.map Request.leaf).reverse ∧
      GeneralBorrowWildcardRelatednessBounds.Dominates exposedLocation.exposedCache final.parent ∧
      (∀ leaf ∈ requests.map Request.leaf, GeneralBorrowExposureHistoryBounds.reads exposedLocation.exposedCache leaf = 1 ∧
        GeneralBorrowExposureHistoryBounds.writes exposedLocation.exposedCache leaf = 0) := by
  let seed := GeneralBorrowFullSharedSeed.input capacity nonzero rootTag childTag different
  have good := GeneralBorrowFullSharedSeed.state capacity nonzero rootTag childTag different
  have fresh : ∀ tag ∈ tags, GeneralBorrowTagMap.Fresh seed.tree.tagMapping tag := by
    intro tag member row present
    change row ∈ (GeneralBorrowFullSharedSeed.tree capacity nonzero rootTag).tagMapping.mapping at present
    rw [GeneralBorrowFullSharedSeed.tree_eq] at present
    have same := Array.mem_singleton.mp present
    subst row
    intro equal
    apply rootUnused
    change rootTag = tag at equal
    rw [equal]
    exact member
  have initialSize : seed.tree.tagMapping.mapping.size = 1 := by
    change (GeneralBorrowFullSharedSeed.tree capacity nonzero rootTag).tagMapping.mapping.size = 1
    rw [GeneralBorrowFullSharedSeed.tree_eq];rfl
  obtain ⟨final,ignoredLocation,history,ignoredGood,allocator,size,spares⟩ :=
    GeneralBorrowFullSharedResources.iterate tags seed GeneralBorrowFullSharedSeed.location good
      (GeneralBorrowGcAllocator.initial rootTag (Size.ofBytes capacity)) fresh distinct childUnused
      (fun step : Fin 0 => Fin.elim0 step) (fun step => Fin.elim0 step) (fun step => Fin.elim0 step)
      (fun _ _ step => Fin.elim0 step) (by rw [initialSize];omega)
  obtain ⟨finalLocation,finalGood,star,unexposed,cache⟩ := GeneralBorrowGeneratedUnexposed.run history
    GeneralBorrowFullSharedSeed.location good
    (seed_star capacity nonzero rootTag childTag different)
    (GeneralBorrowGeneratedUnexposed.seed capacity nonzero rootTag childTag different)
  obtain ⟨requests,leaves,ready⟩ := GeneralBorrowGeneratedExposureReady.requests final.tree finalLocation
    final.parent final.parentNode star finalGood.profile allocator.nodeTags unexposed
  have unique : (requests.map Request.leaf).Nodup := by rw [leaves];exact star.distinct
  have requestLength : requests.length < 65536 := by
    have bounded := children_bound final.tree final.parent final.parentNode star
    have length : requests.length = final.parentNode.children.size := by
      have same := congrArg List.length leaves
      simpa only [List.length_map,Array.length_toList] using same
    have aligned : final.tree.nodes.size = final.tree.tagMapping.mapping.size := final.aligned.symm
    rw [aligned,size,initialSize] at bounded
    rw [length]
    omega
  have emptyCache : finalLocation.exposedCache = {} := cache
  obtain ⟨complete,exposedLocation,locations,counted,dominates,self⟩ := run_counts requests final.tree finalLocation
    final.len final.parent final.parentNode protections finalGood.locations ready unique emptyCache requestLength
  have length : final.len = capacity := history.length
  exact ⟨final,finalLocation,requests,exposedLocation,history,finalGood,leaves,complete,
    by rw [length] at locations;exact locations,counted,dominates,self⟩
end DuplicatePrefix.GeneralBorrowGeneratedExposureCounts
