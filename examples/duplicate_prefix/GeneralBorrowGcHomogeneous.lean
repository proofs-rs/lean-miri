import duplicate_prefix.GeneralBorrowGcRootInvariant
import duplicate_prefix.GeneralBorrowGcWhileInvariant

namespace DuplicatePrefix.GeneralBorrowGcHomogeneous
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.RangeMapNonempty
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Real GC removal rewrites only the payload of a homogeneous range map. -/
theorem remove (tree : BorrowTree) (capacity : UInt64) (location : LocationTree)
    (homogeneous : tree.locations = RangeMapNonempty.homogeneous capacity location) (index : UniIndex) :
    ∃ next, (source_remove_useless_node tree index).1.locations = RangeMapNonempty.homogeneous capacity next := by
  cases present : tree.nodes.get index with
  | none =>
    unfold_source_remove_useless_node
    simp only [present,Id.run,bind,pure]
    exact ⟨location,homogeneous⟩
  | some node =>
    unfold_source_remove_useless_node
    simp only [present,Id.run,bind,pure]
    rw [homogeneous]
    refine ⟨{location with perms := location.perms.remove index, exposedCache := location.exposedCache.remove index},?_⟩
    simp [RangeMapNonempty.homogeneous,DedupRangeMap.modifyAll]

/-- The exact postorder walker keeps the single stored interval, even while
its payload changes as dead leaf permissions/caches are removed. -/
theorem children (tree : BorrowTree) (capacity : UInt64) (location : LocationTree)
    (initial : tree.locations = homogeneous capacity location) (root : UniIndex) (live : Array BorTag) :
    ∃ next, (gc_root_children tree root live).tree.locations = homogeneous capacity next := by
  apply GeneralBorrowGcWhileInvariant.preserves (fun current => ∃ next, current.locations = homogeneous capacity next)
  · intro current index good
    obtain ⟨location,known⟩ := good
    exact remove current capacity location known index
  · intro current index oldNode newNode present same good
    exact good
  · exact ⟨location,initial⟩

/-- Thorough merging has no adjacency check to fail for a single interval. -/
theorem merge (capacity : UInt64) (location : LocationTree) :
    (homogeneous capacity location).mergeAdjacentThorough = ⟨homogeneous capacity location,.ok ()⟩ := by
  unfold DedupRangeMap.mergeAdjacentThorough
  simp [homogeneous,←Array.forIn_toList,bind,pure,Id.run]

end DuplicatePrefix.GeneralBorrowGcHomogeneous
