import duplicate_prefix.GeneralBorrowGcStarWalk
import duplicate_prefix.GeneralBorrowGcHomogeneous

namespace DuplicatePrefix.GeneralBorrowGcStarComplete
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcWalker DuplicatePrefix.GeneralBorrowGcRangeClean
open DuplicatePrefix.RangeMapNonempty
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Once the sole root walk succeeds, final normalization and range merging
change only location data. This frame also includes range-merge error states. -/
theorem nodes (tree : BorrowTree) (root : UniIndex) (live : Array BorTag)
    (roots : tree.roots = #[root]) (success : (source_gc_children tree root live).outcome = .ok ()) :
    (tree.removeUnreachableTags live).tree.nodes = (source_gc_children tree root live).tree.nodes := by
  unfold BorrowTree.removeUnreachableTags
  rw [roots]
  simp only [Id.run,bind,pure,←Array.forIn_toList,
    show (#[root] : Array UniIndex).toList = [root] from rfl,List.forIn_cons,List.forIn_nil]
  rw [show (gc_root_children tree root live).outcome = .ok () from success]
  simp only [bind,pure]
  split <;> rfl

/-- Full production GC on a one-root star with a homogeneous location map
succeeds, for any live-tag set. No GC-success or intermediate trace is a premise. -/
theorem complete (tree : BorrowTree) (root : UniIndex) (node : TreeNode) (live : Array BorTag)
    (capacity : UInt64) (location : LocationTree) (initial : tree.locations = homogeneous capacity location)
    (roots : tree.roots = #[root]) (present : tree.nodes.get root = some node)
    (distinct : node.children.toList.Nodup) (notChild : root ∉ node.children.toList)
    (leaves : ∀ index ∈ node.children.toList, ∃ child,
      tree.nodes.get index = some child ∧ child.children = #[])
    (bounded : node.children.size ≤ tree.nodes.size) :
    (tree.removeUnreachableTags live).outcome = .ok () ∧
    ∃ next, (tree.removeUnreachableTags live).tree.locations = homogeneous capacity next := by
  obtain ⟨after,kept,walked,rootPresent,size,folded⟩ :=
    GeneralBorrowGcStarWalk.complete tree root node live present distinct notChild leaves bounded
  have success : (source_gc_children tree root live).outcome = .ok () := by rw [walked]
  obtain ⟨postLocation,postLocations⟩ := GeneralBorrowGcHomogeneous.children tree capacity location initial root live
  have merged := GeneralBorrowGcHomogeneous.merge capacity (gc_source_trim_location postLocation)
  unfold BorrowTree.removeUnreachableTags
  rw [roots]
  simp only [Id.run,bind,pure,←Array.forIn_toList,show (#[root] : Array UniIndex).toList = [root] from rfl,List.forIn_cons,List.forIn_nil]
  rw [show (gc_root_children tree root live).outcome = .ok () from success]
  simp only [bind,pure]
  have normalized : ((gc_root_children tree root live).tree.locations.modifyAll
      (fun _ location => gc_source_trim_location location)) = homogeneous capacity (gc_source_trim_location postLocation) := by
    rw [postLocations]
    simp [homogeneous,DedupRangeMap.modifyAll]
  rw [normalized,merged]
  exact ⟨rfl,_,rfl⟩

end DuplicatePrefix.GeneralBorrowGcStarComplete
