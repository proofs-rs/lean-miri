import duplicate_prefix.GeneralBorrowGcWhileInvariant
import duplicate_prefix.GeneralBorrowGcRootInvariant
import duplicate_prefix.GeneralBorrowFreshGeometry

namespace DuplicatePrefix.GeneralBorrowGcPartitionGeometry
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Actual all-location payload mutation retains every interval boundary. -/
theorem modify_all (map : DedupRangeMap α) (modify : ByteRange → α → α)
    (well : map.WellFormed) :
    (map.modifyAll modify).WellFormed ∧ (map.modifyAll modify).size = map.size := by
  apply GeneralBorrowFreshGeometry.ranges_frame map (map.modifyAll modify) _ well
  simp [DedupRangeMap.modifyAll,Array.map_map]

/-- Real GC node removal changes location payloads but not partition geometry. -/
theorem remove (tree : BorrowTree) (index : UniIndex) (well : tree.locations.WellFormed) :
    (source_remove_useless_node tree index).1.locations.WellFormed ∧
    (source_remove_useless_node tree index).1.locations.size = tree.locations.size := by
  cases present : tree.nodes.get index with
  | none =>
    unfold_source_remove_useless_node
    simp only [present,Id.run,pure]
    exact ⟨well,True.intro⟩
  | some node =>
    unfold_source_remove_useless_node
    simp only [present,Id.run,pure]
    exact modify_all tree.locations _ well

/-- The full exact postorder walker retains map well-formedness and byte
capacity. This data preservation includes errors, without certifying success. -/
theorem children (tree : BorrowTree) (root : UniIndex) (live : Array BorTag)
    (well : tree.locations.WellFormed) :
    (gc_root_children tree root live).tree.locations.WellFormed ∧
    (gc_root_children tree root live).tree.locations.size = tree.locations.size := by
  let P := fun current : BorrowTree => current.locations.WellFormed ∧ current.locations.size = tree.locations.size
  apply GeneralBorrowGcWhileInvariant.preserves P
  · intro current index good
    have removed := remove current index good.1
    exact ⟨removed.1,removed.2.trans good.2⟩
  · intro current index oldNode newNode present same good
    exact good
  · exact ⟨well,rfl⟩

end DuplicatePrefix.GeneralBorrowGcPartitionGeometry
