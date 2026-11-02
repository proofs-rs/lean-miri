import duplicate_prefix.GeneralBorrowGeneratedExposureReady
import duplicate_prefix.GeneralBorrowExposedProtocolWrite
namespace DuplicatePrefix.GeneralBorrowGeneratedExposedWrite
open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshMetadataChildShared DuplicatePrefix.GeneralBorrowFullSharedStep
open DuplicatePrefix.GeneralBorrowGeneratedStarShape DuplicatePrefix.GeneralBorrowExposeReadFold
open DuplicatePrefix.GeneralBorrowExposedStarFormation DuplicatePrefix.GeneralBorrowExposedProtocolWrite
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- Actual allocation, positive full-slice Read/shared generation, exposure
of every child and root, and a real full-range root Write. All metadata,
operation completions, cache counters and recurring State are derived.
The explicit history budget bounds actual UInt16 counters within Lean alone.
This protocol does not yet include arbitrary mixed histories or GC. -/
theorem generate (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag childTag : BorTag)
    (different : rootTag ≠ childTag) (tags : List BorTag) (distinct : tags.Nodup)
    (rootUnused : rootTag ∉ tags) (childUnused : childTag ∉ tags)
    (short : 2+tags.length < 65536) :
    let seed := GeneralBorrowFullSharedSeed.input capacity nonzero rootTag childTag different
    ∃ (final : Input) (exposed : GeneralBorrowExposedStarFormation.Output final),
      GeneralBorrowFullSharedRepeat.Run seed tags final ∧
      (operation final exposed).status = .Completed ∧
      Nonempty (GeneralBorrowPartitionState.State (operation final exposed).tree final.parent final.len) ∧
      (∀ index node,(operation final exposed).tree.nodeAt index = some node → node.isExposed = true) ∧
      ∃ postLocation, (operation final exposed).tree.locations = RangeMapNonempty.homogeneous capacity postLocation ∧
        GeneralBorrowExposureHistoryBounds.reads postLocation.exposedCache final.parent = 1 ∧
        GeneralBorrowExposureHistoryBounds.writes postLocation.exposedCache final.parent = 1 ∧
        ∀ query,query ≠ final.parent → GeneralBorrowExposureHistoryBounds.reads postLocation.exposedCache query = 0 ∧
          GeneralBorrowExposureHistoryBounds.writes postLocation.exposedCache query = 0 := by
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
  have finalRoom : final.tree.nodes.size+4 ≤ 4294967295 := by
    have aligned : final.tree.nodes.size = final.tree.tagMapping.mapping.size := final.aligned.symm
    rw [aligned,size,initialSize]
    omega
  have counterRoom : final.parentNode.children.size+1 < 65536 := by
    have bounded := children_bound final.tree final.parent final.parentNode star
    have aligned : final.tree.nodes.size = final.tree.tagMapping.mapping.size := final.aligned.symm
    rw [aligned,size,initialSize] at bounded
    omega
  obtain ⟨exposed⟩ := form final finalLocation finalGood star allocator finalRoom unexposed cache counterRoom
  obtain ⟨complete,state,flags,postLocation,locations,counts⟩ := write final exposed
  have length : final.len = capacity := history.length
  refine ⟨final,exposed,history,complete,state,flags,postLocation,?_,counts⟩
  rw [←length]
  exact locations
end DuplicatePrefix.GeneralBorrowGeneratedExposedWrite
