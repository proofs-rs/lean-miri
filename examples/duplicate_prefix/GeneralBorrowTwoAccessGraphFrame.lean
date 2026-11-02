import duplicate_prefix.GeneralBorrowFreshReadFrame
namespace DuplicatePrefix.GeneralBorrowTwoAccessGraphFrame
open Miri.ABI Miri.Memory Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
/-- Two physical ranged accesses preserve graph metadata on every outcome. -/
theorem frame (tree : BorrowTree) (tag : BorTag) (offset count : UInt64) (tags : ProtectedTags) :
    let read:=tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes count) .Read tags .VisitChildrenOfAccessed
    let write:=read.tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes (offset+count)) (Size.ofBytes count) .Write tags .VisitChildrenOfAccessed
    write.tree={tree with locations:=write.tree.locations} := by
  dsimp only
  have first:=GeneralBorrowFreshReadFrame.frame tree (.concrete tag) (Size.ofBytes offset) (Size.ofBytes count) .Read tags .VisitChildrenOfAccessed
  have second:=GeneralBorrowFreshReadFrame.frame
    (tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes count) .Read tags .VisitChildrenOfAccessed).tree
    (.concrete tag) (Size.ofBytes (offset+count)) (Size.ofBytes count) .Write tags .VisitChildrenOfAccessed
  exact second.trans (congrArg (fun before : BorrowTree=>{before with locations:=
    ((tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes count) .Read tags .VisitChildrenOfAccessed).tree.performBorrowAccessRange
      (.concrete tag) (Size.ofBytes (offset+count)) (Size.ofBytes count) .Write tags .VisitChildrenOfAccessed).tree.locations}) first)
end DuplicatePrefix.GeneralBorrowTwoAccessGraphFrame
