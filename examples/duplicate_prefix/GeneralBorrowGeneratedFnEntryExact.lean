import duplicate_prefix.GeneralBorrowGeneratedFnEntryHistory
import duplicate_prefix.GeneralBorrowForestFnEntry
namespace DuplicatePrefix.GeneralBorrowGeneratedFnEntryExact
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestGeneratedTagHistoryData
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- Protected homogeneous Default specialization is exactly the existing real
FnEntry operation, with its returned singleton frame retained on the source
history stack. This is an equality of actual evaluators, including failures. -/
theorem default_operation (id : AllocId) (state : Snapshot) (parent : BorTag)
    (offset len : UInt64) (mode : ChildrenVisitMode) :
    GeneralBorrowGeneratedFnEntry.operation id state parent (Size.ofBytes offset) (Size.ofBytes len)
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true mode =
    (GeneralBorrowForestFnEntry.operation state.tree state.global {} id parent offset len mode).map
      (fun output => (⟨⟨output.child.tree,output.global,state.frames.push (output.tag,output.frame)⟩,
        output.access,output.child⟩ : GeneralBorrowGeneratedFnEntry.Output)) := by
  unfold GeneralBorrowGeneratedFnEntry.operation GeneralBorrowForestFnEntry.operation
  cases allocated : state.global.newPointerTag with
  | error error => rfl
  | ok pair => rcases pair with ⟨advanced,tag⟩;rfl
end DuplicatePrefix.GeneralBorrowGeneratedFnEntryExact
