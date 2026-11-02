import duplicate_prefix.GeneralBorrowSharedBankRead
import duplicate_prefix.GeneralBorrowSharedBankNodes
import duplicate_prefix.GeneralBorrowSharedConstructorReadStage

namespace DuplicatePrefix.GeneralBorrowSharedBankAdvance
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowSharedBankState DuplicatePrefix.GeneralBorrowFreshSharedSequence
open DuplicatePrefix.GeneralBorrowRecursiveSharedHistory DuplicatePrefix.GeneralRangeMapOrigins

/-- An actual chosen-parent stage extends the bank by its fresh child while
retaining every previously selectable handle and its range-local Read owner. -/
noncomputable def next {root : UniIndex} {offset len : UInt64}
    (s : GeneralBorrowSharedBankState.State root offset len)
    (parent : UniIndex) (member : parent ∈ s.handles) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh s.tree.tagMapping tag) (nonzero : len ≠ 0)
    (room : s.tree.nodes.size+5 ≤ 4294967295) : GeneralBorrowSharedBankState.State root offset len := by
  let selected := select s parent member
  let d := supplied selected tag fresh nonzero
  let actual := GeneralBorrowRecursiveSharedHistory.next selected tag fresh nonzero false room
  have readFacts := GeneralBorrowSharedBankRead.run s parent member tag fresh nonzero
  exact {
    tree := actual.tree, resources := actual.resources
    handles := actual.parent :: s.handles
    present := by
      intro target inBank
      rcases List.mem_cons.mp inBank with same | old
      · subst target;exact ⟨actual.node,actual.present⟩
      · exact GeneralBorrowSharedBankNodes.retained s parent member tag fresh nonzero room target old
    bounds := actual.bounds
    owned := by
      intro target inBank
      rcases List.mem_cons.mp inBank with same | old
      · subst target
        intro position valid positive before after
        have owner := (actual.owned position valid positive before after).1
        simpa [actual,selected,select,GeneralBorrowRecursiveSharedHistory.next,registered] using owner
      · exact GeneralBorrowSharedConstructorReadStage.owned s.tree tag parent offset len d (fun _ => false)
          selected.owned target (s.present target old) (readFacts.2 target old) }

theorem handles_length {root : UniIndex} {offset len : UInt64}
    (s : GeneralBorrowSharedBankState.State root offset len)
    (parent : UniIndex) (member : parent ∈ s.handles) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh s.tree.tagMapping tag) (nonzero : len ≠ 0)
    (room : s.tree.nodes.size+5 ≤ 4294967295) :
    (next s parent member tag fresh nonzero room).handles.length = s.handles.length+1 := rfl

theorem size {root : UniIndex} {offset len : UInt64}
    (s : GeneralBorrowSharedBankState.State root offset len)
    (parent : UniIndex) (member : parent ∈ s.handles) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh s.tree.tagMapping tag) (nonzero : len ≠ 0)
    (room : s.tree.nodes.size+5 ≤ 4294967295) :
    (next s parent member tag fresh nonzero room).tree.nodes.size ≤ s.tree.nodes.size+1 :=
  GeneralBorrowRecursiveSharedHistory.next_size (select s parent member) tag fresh nonzero false room
end DuplicatePrefix.GeneralBorrowSharedBankAdvance
