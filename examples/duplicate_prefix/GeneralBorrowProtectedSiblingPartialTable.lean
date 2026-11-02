import duplicate_prefix.GeneralBorrowProtectedSiblingPartialComplete
import duplicate_prefix.GeneralBorrowProtectedSiblingWindowTable
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingPartialTable
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProtectedSiblingPartial GeneralBorrowProtectedSiblingWindowTable
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem loop {capacity : UInt64} (windows : List (Window capacity)) (before after : Snapshot)
    (actual : GeneralBorrowProtectedSiblingPartial.loop windows before = .ok after)
    (covered : Covered before.global before.frame) : Covered after.global after.frame := by
  induction windows generalizing before with
  | nil => cases actual;exact covered
  | cons window rest ih =>
    unfold GeneralBorrowProtectedSiblingPartial.loop at actual
    cases current : GeneralBorrowForestFnEntry.operation before.tree before.global before.frame
        GeneralBorrowProtectedSiblingGenerationWindowSeed.allocation BorTag.one window.offset window.len .VisitChildrenOfAccessed with
    | error error => simp [current,bind,Except.bind] at actual
    | ok output =>
      simp only [current,bind,Except.bind] at actual
      exact ih _ actual (GeneralBorrowProtectedSiblingWindowTable.step _ _ _ _ _ _ _ _ output current covered)

theorem generated (capacity : UInt64) (windows : List (Window capacity)) (state : Snapshot)
    (actual : operation capacity windows = .ok state) : Covered state.global state.frame := by
  unfold operation at actual
  rw [GeneralBorrowProtectedSiblingGenerationWindowSeed.root_allocation] at actual
  simp only [bind,Except.bind] at actual
  exact loop windows _ state actual (by intro row member;simpa [GeneralBorrowProtectedSiblingGenerationWindowSeed.global] using member)
end DuplicatePrefix.GeneralBorrowProtectedSiblingPartialTable
