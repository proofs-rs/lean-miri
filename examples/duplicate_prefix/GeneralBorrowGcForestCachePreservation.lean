import duplicate_prefix.GeneralBorrowGcCachePreservation
import duplicate_prefix.GeneralBorrowGcSurvivingRootPaths

namespace DuplicatePrefix.GeneralBorrowGcForestCachePreservation
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowForest
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowExposureCardinality DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- FULL actual GC preserves every partition's exposed-support cardinality
cache on arbitrary finite forests and ordered root arrays (including duplicates
and empty lists). Initial graph/UInt32 slots/partition/liveness/cache contracts
are explicit. Every actual component traversal, surviving-ancestor equivalence,
exposed-source retention and final cache equation is internally derived. -/
theorem collect (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (forest : Forest (source_normal_projection tree location protections).topology)
    (depth : ParentDepth tree.nodes) (closed : GeneralBorrowGraph.ChildNodes tree)
    (fits : tree.nodes.size ≤ 4294967296)
    (rootNodes : ∀ root ∈ tree.roots.toList,∃ node,tree.nodes.get root = some node ∧ node.parent = none)
    (well : tree.locations.WellFormed) (live : Array BorTag)
    (exposedLive : GeneralBorrowGcExposedRetained.ExposedLive tree live)
    (initial : Every (fun location => LocationCoherent tree location protections) tree.locations) :
    (tree.removeUnreachableTags live).outcome = .ok () ∧
      Every (fun location => LocationCoherent (tree.removeUnreachableTags live).tree location protections)
        (tree.removeUnreachableTags live).tree.locations := by
  refine ⟨(GeneralBorrowGcForestComplete.complete tree location protections forest depth closed fits rootNodes well live).1,?_⟩
  exact GeneralBorrowGcCachePreservation.transfer tree (tree.removeUnreachableTags live).tree protections
    (GeneralBorrowGcNodeMetadata.collect tree live)
    (GeneralBorrowGcExposedRetained.collect tree live exposedLive)
    (GeneralBorrowGcSurvivingRootPaths.collect tree location protections forest depth closed fits rootNodes well live)
    (GeneralBorrowGcCacheFrame.collect tree protections depth initial live)

end DuplicatePrefix.GeneralBorrowGcForestCachePreservation
