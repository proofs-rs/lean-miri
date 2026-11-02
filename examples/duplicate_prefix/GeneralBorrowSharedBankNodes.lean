import duplicate_prefix.GeneralBorrowSharedBankState
import duplicate_prefix.GeneralBorrowFreshSharedStagePaths

namespace DuplicatePrefix.GeneralBorrowSharedBankNodes
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowSharedBankState DuplicatePrefix.GeneralBorrowRecursiveSharedHistory
open DuplicatePrefix.GeneralBorrowFreshSharedSequence

/-- Every selectable old handle is still present after an actual chosen-parent
Read and shared constructor, including allocator reuse. -/
theorem retained {root : UniIndex} {offset len : UInt64}
    (s : GeneralBorrowSharedBankState.State root offset len)
    (parent : UniIndex) (member : parent ∈ s.handles) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh s.tree.tagMapping tag) (nonzero : len ≠ 0)
    (room : s.tree.nodes.size+5 ≤ 4294967295)
    (target : UniIndex) (targetMember : target ∈ s.handles) :
    ∃ node, (next (select s parent member) tag fresh nonzero false room).tree.nodeAt target = some node := by
  obtain ⟨node,present⟩ := s.present target targetMember
  let selected := select s parent member
  let d := supplied selected tag fresh nonzero
  obtain ⟨after,presentAfter,_,_⟩ := GeneralBorrowFreshSharedStagePaths.old_node
    s.tree tag parent offset len d {} false (fun _ => false) selected.owned target node present
  exact ⟨after,presentAfter⟩

/-- Actual freshness excludes every selectable old handle from the inserted
slot, independently of append versus reuse. -/
theorem different {root : UniIndex} {offset len : UInt64}
    (s : GeneralBorrowSharedBankState.State root offset len)
    (parent : UniIndex) (member : parent ∈ s.handles) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh s.tree.tagMapping tag) (nonzero : len ≠ 0)
    (target : UniIndex) (targetMember : target ∈ s.handles) :
    target ≠ index (supplied (select s parent member) tag fresh nonzero) := by
  obtain ⟨node,present⟩ := s.present target targetMember
  let d := supplied (select s parent member) tag fresh nonzero
  have vacant := GeneralBorrowFreshSharedWithinStages.slot_vacant s.tree d.depth parent d.slot
  exact GeneralBorrowFreshReuseNode.parent_not_vacant s.tree.nodes (index d) target node vacant present
end DuplicatePrefix.GeneralBorrowSharedBankNodes
