import duplicate_prefix.GeneralBorrowPhysicalReadable
import duplicate_prefix.GeneralBorrowProtectedReadSingleRoot
namespace DuplicatePrefix.GeneralBorrowPhysicalReadableLocation
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

theorem location (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor root : UniIndex) (mode : ChildrenVisitMode) (range : ByteRange)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (fits : tree.nodes.data.size ≤ 4294967296) (depth : ParentDepth tree.nodes)
    (children : GeneralBorrowGraph.ChildNodes tree) (node : TreeNode) (present : tree.nodeAt anchor = some node)
    (roots : tree.roots = #[root]) (covered : GeneralBorrowGraph.RootsCover tree)
    (initial : GeneralBorrowPhysicalReadable.Profile tree location protections) :
    source_access_status (source_tree_access_at tree location (some anchor) .Read protections mode range) = none ∧
      GeneralBorrowPhysicalReadable.Profile tree
        (source_access_location (source_tree_access_at tree location (some anchor) .Read protections mode range)) protections := by
  have valid : anchor.toNat < (source_normal_projection tree location protections).topology.nodes.size := by
    obtain ⟨valid,_⟩ := array_of_node tree anchor node present
    unfold_general_projection;unfold_general_topology
    simpa only [Array.size_mapIdx,Array.size_map] using valid
  have pointwise := GeneralBorrowPhysicalReadable.compatible tree location protections anchor node present depth fits initial
  refine ⟨GeneralBorrowProtectedReadSingleRoot.access_at tree location protections anchor root mode range forest valid pointwise
    depth children node present roots covered,?_⟩
  rw [GeneralBorrowProtectedReadSingleRoot.single_root_location tree location protections anchor root mode range forest valid pointwise
    depth children node present roots covered]
  exact (GeneralBorrowPhysicalReadable.normal tree location protections anchor mode forest fits depth children node present initial).2.2

end DuplicatePrefix.GeneralBorrowPhysicalReadableLocation
