import duplicate_prefix.GeneralBorrowGcDfsFormation
import duplicate_prefix.GeneralBorrowGcPartitionGeometry
import duplicate_prefix.GeneralRangeMapThoroughComplete

namespace DuplicatePrefix.GeneralBorrowGcTreeComplete
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcWalker DuplicatePrefix.GeneralBorrowGcRangeClean
open DuplicatePrefix.GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Full REAL production GC with one listed root in an arbitrary finite reciprocal
forest and arbitrary well-formed partition map completes. The original graph may have
arbitrary branching/depth, free slots and live-tag set. The source DFS Plan and
budget, node callbacks, final normalization and thorough merge are all derived;
no GC outcome/intermediate success is a premise. This proves completion and
range geometry, not final reciprocal topology or ownership reconstruction. -/
theorem complete (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (children : GeneralBorrowGraph.ChildNodes tree) (root : UniIndex) (node : TreeNode) (live : Array BorTag)
    (present : tree.nodes.get root = some node) (roots : tree.roots = #[root]) (well : tree.locations.WellFormed) :
    (tree.removeUnreachableTags live).outcome = .ok () ∧
    (tree.removeUnreachableTags live).tree.locations.WellFormed ∧
    (tree.removeUnreachableTags live).tree.locations.size = tree.locations.size := by
  obtain ⟨after,walked,_⟩ := GeneralBorrowGcDfsFormation.children_complete tree location protections forest children root node present live
  have success : (source_gc_children tree root live).outcome = .ok () := by rw [walked]
  have walkedGeometry := GeneralBorrowGcPartitionGeometry.children tree root live well
  let normalized := (gc_root_children tree root live).tree.locations.modifyAll (fun _ location => gc_source_trim_location location)
  have normalizedGeometry := GeneralBorrowGcPartitionGeometry.modify_all (gc_root_children tree root live).tree.locations
    (fun _ location => gc_source_trim_location location) walkedGeometry.1
  have merged := GeneralRangeMapThoroughComplete.complete normalized normalizedGeometry.1
  unfold BorrowTree.removeUnreachableTags
  rw [roots]
  simp only [Id.run,bind,pure,←Array.forIn_toList,List.forIn_cons,List.forIn_nil]
  rw [show (gc_root_children tree root live).outcome = .ok () from success]
  change (match normalized.mergeAdjacentThorough.outcome with
    | .error error => ({tree := {(gc_root_children tree root live).tree with locations := normalized.mergeAdjacentThorough.state},outcome := .error (.RangeMerge error)} : BorrowTree.TreeGcResult)
    | .ok () => ({tree := {(gc_root_children tree root live).tree with locations := normalized.mergeAdjacentThorough.state},outcome := .ok ()} : BorrowTree.TreeGcResult)).outcome = .ok () ∧ _
  rw [merged.1]
  exact ⟨rfl,merged.2.1,merged.2.2.trans (normalizedGeometry.2.trans walkedGeometry.2)⟩

end DuplicatePrefix.GeneralBorrowGcTreeComplete
