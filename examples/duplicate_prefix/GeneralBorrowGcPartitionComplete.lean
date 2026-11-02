import duplicate_prefix.GeneralBorrowGcPartitionGeometry
import duplicate_prefix.GeneralBorrowGcStarWalk
import duplicate_prefix.GeneralBorrowGeneratedStarShape
import duplicate_prefix.GeneralRangeMapThoroughComplete

namespace DuplicatePrefix.GeneralBorrowGcPartitionComplete
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcWalker DuplicatePrefix.GeneralBorrowGcRangeClean DuplicatePrefix.GeneralBorrowGeneratedStarShape
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Full production GC on a one-root star with ANY well-formed partition map
completes and retains well-formedness and byte capacity. No homogeneous profile,
GC outcome or intermediate operation success is supplied as a premise. -/
theorem complete (tree : BorrowTree) (root : UniIndex) (node : TreeNode) (live : Array BorTag)
    (star : Star tree root node) (roots : tree.roots = #[root]) (well : tree.locations.WellFormed) :
    (tree.removeUnreachableTags live).outcome = .ok () ∧
    (tree.removeUnreachableTags live).tree.locations.WellFormed ∧
    (tree.removeUnreachableTags live).tree.locations.size = tree.locations.size := by
  have notChild : root ∉ node.children.toList := by
    intro member;exact ((star.children root).mp member).1 rfl
  have leaves : ∀ index ∈ node.children.toList, ∃ child,
      tree.nodes.get index = some child ∧ child.children = #[] := by
    intro index member
    obtain ⟨different,child,present⟩ := (star.children index).mp member
    exact ⟨child,present,(star.leaves index child present different).2⟩
  obtain ⟨after,kept,walked,rootPresent,size,folded⟩ :=
    GeneralBorrowGcStarWalk.complete tree root node live star.present star.distinct notChild leaves
      (children_bound tree root node star)
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

end DuplicatePrefix.GeneralBorrowGcPartitionComplete
