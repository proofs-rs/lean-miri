import duplicate_prefix.GeneralBorrowGcPartitionGeometry
import duplicate_prefix.GeneralRangeMapThoroughComplete

namespace DuplicatePrefix.GeneralBorrowGcForestGeometry
open DuplicatePrefix.GeneralBorrowGcRangeClean
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree

/-- Full production GC preserves interval-map well-formedness and allocation
byte capacity for arbitrary node graphs. Child-walk error prefixes are included
as data states; no successful GC outcome is asserted. -/
theorem preserves (tree : BorrowTree) (live : Array BorTag) (well : tree.locations.WellFormed) :
    (tree.removeUnreachableTags live).tree.locations.WellFormed ∧
      (tree.removeUnreachableTags live).tree.locations.size = tree.locations.size := by
  let P := fun current : BorrowTree => current.locations.WellFormed ∧ current.locations.size = tree.locations.size
  apply GeneralBorrowGcRootInvariant.preserves P tree live ⟨well,rfl⟩
  · intro current root initial
    have geometry := GeneralBorrowGcPartitionGeometry.children current root live initial.1
    exact ⟨geometry.1,geometry.2.trans initial.2⟩
  · intro current initial
    have normalized := GeneralBorrowGcPartitionGeometry.modify_all current.locations
      (fun _ location => gc_source_trim_location location) initial.1
    have merged := GeneralRangeMapThoroughComplete.complete _ normalized.1
    exact ⟨merged.2.1,merged.2.2.trans (normalized.2.trans initial.2)⟩
end DuplicatePrefix.GeneralBorrowGcForestGeometry
