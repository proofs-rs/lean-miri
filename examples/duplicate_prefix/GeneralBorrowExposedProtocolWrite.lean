import duplicate_prefix.GeneralBorrowExposedStarFormation
import duplicate_prefix.GeneralBorrowHomogeneousFullAccess
namespace DuplicatePrefix.GeneralBorrowExposedProtocolWrite
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshMetadataChildShared DuplicatePrefix.GeneralBorrowExposedStarFormation
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposureHistoryBounds
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

def operation (input : Input) (s : GeneralBorrowExposedStarFormation.Output input) :=
  GeneralBorrowPartitionState.operation s.tree s.state.node.tag 0 input.len .Write

/-- The real full-range root Write after actual leaf/root exposure has exact
remaining counters, preserves all exposed flags, and restores recurring State. -/
theorem write (input : Input) (s : GeneralBorrowExposedStarFormation.Output input) :
    (operation input s).status = .Completed ∧
    Nonempty (GeneralBorrowPartitionState.State (operation input s).tree input.parent input.len) ∧
    (∀ index node,(operation input s).tree.nodeAt index = some node → node.isExposed = true) ∧
    ∃ postLocation, (operation input s).tree.locations = RangeMapNonempty.homogeneous input.len postLocation ∧
      reads postLocation.exposedCache input.parent = 1 ∧ writes postLocation.exposedCache input.parent = 1 ∧
      ∀ query,query ≠ input.parent → reads postLocation.exposedCache query = 0 ∧ writes postLocation.exposedCache query = 0 := by
  have fits : s.tree.nodes.size ≤ 4294967296 := by have bound := s.state.room;omega
  obtain ⟨⟨forest⟩,owned⟩ := GeneralBorrowStarOwnership.location_owned s.tree input.parent s.node s.star s.location s.profile fits
  have tagged := s.state.allocator.nodeTags input.parent s.state.node s.state.star.present
  have full := GeneralBorrowHomogeneousFullAccess.full s.tree input.parent s.node s.state.node.tag input.len input.nonzero s.location .Write
    tagged s.locations s.star s.state.roots forest owned
  have actual : (operation input s).tree = {s.tree with locations := RangeMapNonempty.homogeneous input.len (s.tree.performNormalAccessAt s.location input.parent .Write {} .VisitChildrenOfAccessed).location} := full.2
  have counted := GeneralBorrowExposedStarWrite.normal s.tree s.location input.parent s.node s.star s.profile fits s.exposed s.counts
  have access := GeneralBorrowPartitionState.access s.tree input.parent input.len s.state 0 input.len .Write (by simp)
  obtain ⟨post,tag⟩ := Classical.choice access.2.1
  refine ⟨full.1,⟨post⟩,?_,(s.tree.performNormalAccessAt s.location input.parent .Write {} .VisitChildrenOfAccessed).location,?_,counted.2⟩
  · intro index node present
    rw [actual] at present
    exact s.exposed index node present
  · rw [actual]
end DuplicatePrefix.GeneralBorrowExposedProtocolWrite
