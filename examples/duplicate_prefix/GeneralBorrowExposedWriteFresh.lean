import duplicate_prefix.GeneralBorrowExposedWriteDisabled
import duplicate_prefix.GeneralBorrowExposureMapFrame
namespace DuplicatePrefix.GeneralBorrowExposedWriteFresh
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshMetadataChildShared DuplicatePrefix.GeneralBorrowExposedProtocolWrite
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Actual leaf/root exposure and subsequent full Write retain the exact
allocator tag mapping, so unused call/reserved tags remain fresh. -/
theorem mapping (input : Input) (s : GeneralBorrowExposedStarFormation.Output input) :
    (operation input s).tree.tagMapping = input.tree.tagMapping := by
  have exposed := GeneralBorrowExposureMapFrame.expose
    (GeneralBorrowExposeReadFold.run {} s.requests input.tree).tree {} input.parentTag
  rw [s.rootEq] at exposed
  have mapped : s.tree.tagMapping = input.tree.tagMapping := exposed.trans
    (GeneralBorrowExposureMapFrame.run s.requests input.tree {})
  have accessed := GeneralBorrowPartitionState.access s.tree input.parent input.len s.state 0 input.len .Write (by simp)
  exact accessed.2.2.2.trans mapped
end DuplicatePrefix.GeneralBorrowExposedWriteFresh
