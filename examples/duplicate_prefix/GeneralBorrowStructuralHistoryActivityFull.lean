import duplicate_prefix.GeneralBorrowStructuralHistoryGeneral
import duplicate_prefix.GeneralBorrowFreshActiveWithin
namespace DuplicatePrefix.GeneralBorrowStructuralHistoryActivityFull
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshActiveWithin GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

/-- A well-formed allocation partition itself derives whole-allocation Write
activity confinement for every slot. This does not assert any permission is
writable, present, initialized or allowed by the current protector table. -/
theorem full (tree : BorrowTree) (index : UniIndex) (well : tree.locations.WellFormed) :
    ActiveWithin tree index .Write 0 tree.locations.size.bytes := by
  intro point location atPoint state stored accessed kind associated
  obtain ⟨position,valid,startPoint,pointStop,dataEq⟩ := atPoint
  have nonempty : 0<tree.locations.entries.size := by omega
  have lastValid : tree.locations.entries.size-1<tree.locations.entries.size := by omega
  have lastSize := GeneralRangeMapGeometry.size_last tree.locations nonempty
  have upper : tree.locations.entries[position].range.stop.toNat≤tree.locations.size.bytes.toNat := by
    rw [lastSize]
    by_cases last : position=tree.locations.entries.size-1
    · subst position;exact Nat.le_refl _
    · have earlier : position<tree.locations.entries.size-1 := by omega
      have before := GeneralRangeMapGeometry.stop_le_start tree.locations well position (tree.locations.entries.size-1) earlier lastValid
      have positive := (GeneralRangeMapGeometry.facts tree.locations well (by omega)).2.1 (tree.locations.entries.size-1) lastValid
      omega
  exact ⟨by simp,by omega,by intro impossible;cases impossible⟩

/-- Every reached structural-history prefix forms the original full-buffer
activity bound, independently of which source operations completed or failed. -/
theorem from_new (tag : BorTag) (size : Size) (events : List GeneralBorrowStructuralHistoryGeneral.Event)
    (scheduled : GeneralBorrowStructuralHistoryGeneral.Schedule (BorrowTree.new tag size) events) (count : Nat) (index : UniIndex) :
    ActiveWithin (GeneralBorrowStructuralHistoryGeneral.run (BorrowTree.new tag size) (events.take count)).tree index .Write
      0 (BorrowTree.new tag size).locations.size.bytes := by
  have preserved:=GeneralBorrowStructuralHistoryGeneral.from_new tag size events scheduled count
  have active:=full _ index preserved.1.well
  rw[preserved.2] at active
  exact active
end DuplicatePrefix.GeneralBorrowStructuralHistoryActivityFull
