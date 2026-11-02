import duplicate_prefix.GeneralBorrowGcProvenanceLive
import duplicate_prefix.GeneralBorrowGcForestCachePreservation

namespace DuplicatePrefix.GeneralBorrowGcReportedCachePreservation
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowForest
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowExposureCardinality DuplicatePrefix.GeneralRangeMapState

/-- The actual provenance visitor, plus arbitrary extra tags, supplies the
exposed liveness needed by full forest GC. No liveness or GC-success premise
replaces either real source operation. -/
theorem collect (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (forest : Forest (source_normal_projection tree location protections).topology)
    (depth : ParentDepth tree.nodes) (closed : GeneralBorrowGraph.ChildNodes tree)
    (fits : tree.nodes.size ≤ 4294967296)
    (rootNodes : ∀ root ∈ tree.roots.toList,∃ node,tree.nodes.get root = some node ∧ node.parent = none)
    (well : tree.locations.WellFormed) (extra : Array BorTag)
    (initial : Every (fun location => LocationCoherent tree location protections) tree.locations) :
    let live := tree.provenanceTags ++ extra
    (tree.removeUnreachableTags live).outcome = .ok () ∧
      Every (fun location => LocationCoherent (tree.removeUnreachableTags live).tree location protections)
        (tree.removeUnreachableTags live).tree.locations := by
  apply GeneralBorrowGcForestCachePreservation.collect tree location protections forest depth closed fits rootNodes well
    (tree.provenanceTags ++ extra) ?_ initial
  intro index node present exposed
  apply Array.contains_iff_mem.mpr
  apply Array.mem_append.mpr
  exact Or.inl (Array.contains_iff_mem.mp (GeneralBorrowGcProvenanceLive.provenance tree index node present exposed))

end DuplicatePrefix.GeneralBorrowGcReportedCachePreservation
