import duplicate_prefix.GeneralBorrowFrozenStarWriteMetadata
import duplicate_prefix.GeneralBorrowWriteCacheCardinality
namespace DuplicatePrefix.GeneralBorrowExposedStarWrite
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowWriteCacheCardinality DuplicatePrefix.GeneralBorrowWriteCardinality
open DuplicatePrefix.GeneralBorrowExposureHistoryBounds
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

theorem leaves_indices (root : UniIndex) (indices : List UniIndex)
    (different : ∀ index ∈ indices,index ≠ root) : leaves root (indices.map UniIndex.toNat) = indices := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    simp only [List.map_cons,leaves,List.filterMap_cons,index_self,ite_eq_right (different index (by simp))]
    exact congrArg (List.cons index) (ih (fun other member => different other (by simp [member])))

/-- A real root Write over an exposed generated Frozen star consumes exactly
all leaf Read witnesses and leaves just the exposed Unique root's two counters.
The metadata/permutation are derived internally from the actual traversal. -/
theorem normal (tree : BorrowTree) (location : LocationTree) (root : UniIndex) (rootNode : TreeNode)
    (star : GeneralBorrowGeneratedStarShape.Star tree root rootNode)
    (profile : GeneralBorrowSharedGeneratorProfile.Profile tree location root)
    (fits : tree.nodes.size ≤ 4294967296)
    (exposed : ∀ index node,tree.nodeAt index = some node → node.isExposed = true)
    (counted : Counts location.exposedCache root rootNode.children.toList) :
    let result := tree.performNormalAccessAt location root .Write {} .VisitChildrenOfAccessed
    result.outcome = .ok () ∧ reads result.location.exposedCache root = 1 ∧ writes result.location.exposedCache root = 1 ∧
      ∀ query,query ≠ root → reads result.location.exposedCache query = 0 ∧ writes result.location.exposedCache query = 0 := by
  obtain ⟨events,metadata⟩ := GeneralBorrowFrozenStarWriteMetadata.normal tree location root rootNode star profile fits exposed
  obtain ⟨⟨forest⟩,owned⟩ := GeneralBorrowStarOwnership.location_owned tree root rootNode star location profile fits
  have actualLeaves : leaves root
      (((source_normal_projection tree location {}).performAccess root.toNat .Write .VisitChildrenOfAccessed).visited.map TraversalEvent.node) =
      rootNode.children.toList.reverse := by
    rw [events]
    simp only [List.map_cons,List.map_map,leaves,List.filterMap_cons,index_self,ite_true]
    change leaves root (rootNode.children.toList.reverse.map UniIndex.toNat) = rootNode.children.toList.reverse
    apply leaves_indices
    intro index member
    exact ((star.children index).mp (List.mem_reverse.mp member)).1
  apply normal_complete tree location root rootNode .VisitChildrenOfAccessed star.present star.parentless forest owned metadata
    rootNode.children.toList counted
  rw [actualLeaves]
  exact (List.reverse_perm _).symm
end DuplicatePrefix.GeneralBorrowExposedStarWrite
