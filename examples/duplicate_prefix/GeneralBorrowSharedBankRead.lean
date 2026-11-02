import duplicate_prefix.GeneralBorrowSharedBankState
import duplicate_prefix.GeneralBorrowUnprotectedReadLocalBank

namespace DuplicatePrefix.GeneralBorrowSharedBankRead
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowSharedBankState DuplicatePrefix.GeneralBorrowRecursiveSharedHistory
open DuplicatePrefix.GeneralBorrowFreshSharedSequence DuplicatePrefix.GeneralRangeMapOrigins

/-- Selecting any existing handle gives a real successful Read and preserves
all bank ownership on the requested range, using actual output metadata. -/
theorem run {root : UniIndex} {offset len : UInt64} (s : GeneralBorrowSharedBankState.State root offset len)
    (parent : UniIndex) (member : parent ∈ s.handles) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh s.tree.tagMapping tag) (nonzero : len ≠ 0) :
    let d := supplied (select s parent member) tag fresh nonzero
    (read d {} false).status = .Completed ∧
      ∀ target ∈ s.handles,
        OwnedOn (GeneralBorrowRange.LocationOwned (read d {} false).tree {} target .Read)
          offset (offset+len) (read d {} false).tree.locations := by
  let d := supplied (select s parent member) tag fresh nonzero
  have facts := GeneralBorrowUnprotectedReadLocalBank.preserves s.tree d.parentTag parent d.root s.handles
    (Size.ofBytes offset) (Size.ofBytes len) .VisitChildrenOfAccessed d.nodeFits d.depth d.children
    d.parentNode d.parentPresent d.roots d.covered d.parentTagPresent d.well offset (offset+len)
    (s.owned parent member) s.owned d.bounds (Nat.le_refl _) (Nat.le_refl _)
  change (read d {} false).status = .Completed ∧
    (∀ target ∈ s.handles, OwnedOn (GeneralBorrowRange.LocationOwned s.tree {} target .Read)
      offset (offset+len) (read d {} false).tree.locations) ∧ _ at facts
  have frame := GeneralBorrowFreshReadFrame.frame s.tree (.concrete d.parentTag)
    (Size.ofBytes offset) (Size.ofBytes len) .Read {} .VisitChildrenOfAccessed
  change (read d {} false).tree = {s.tree with locations := (read d {} false).tree.locations} at frame
  have transport (target : UniIndex) (location : LocationTree) :
      GeneralBorrowRange.LocationOwned (read d {} false).tree {} target .Read location =
        GeneralBorrowRange.LocationOwned s.tree {} target .Read location := by
    rw [frame]
    rfl
  refine ⟨facts.1,?_⟩
  intro target member position valid positive before after
  have old := facts.2.1 target member position valid positive before after
  change GeneralBorrowRange.LocationOwned (read d {} false).tree {} target .Read _
  rw [transport]
  exact old
end DuplicatePrefix.GeneralBorrowSharedBankRead
