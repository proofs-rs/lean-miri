import duplicate_prefix.GeneralBorrowForestGeneratedTagHistory
namespace DuplicatePrefix.GeneralBorrowPhysicalReadableRunAppend
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestGeneratedTagHistoryData
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
theorem append (id : AllocId) (state : Snapshot) (before after : List Event) :
    GeneralBorrowForestGeneratedTagHistory.run id state (before++after)=
      let first:=GeneralBorrowForestGeneratedTagHistory.run id state before
      if first.completed then GeneralBorrowForestGeneratedTagHistory.run id first.state after else first := by
  induction before generalizing state with
  | nil => rfl
  | cons event rest ih =>
    cases completed : (step id state event).completed with
    | false => simp only [List.cons_append,GeneralBorrowForestGeneratedTagHistory.run,completed,Bool.false_eq_true,↓reduceIte]
    | true => simpa only [List.cons_append,GeneralBorrowForestGeneratedTagHistory.run,completed,↓reduceIte] using ih (step id state event).state

end DuplicatePrefix.GeneralBorrowPhysicalReadableRunAppend
