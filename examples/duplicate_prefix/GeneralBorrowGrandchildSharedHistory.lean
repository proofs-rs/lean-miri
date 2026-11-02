import duplicate_prefix.GeneralBorrowChildSharedHistory

namespace DuplicatePrefix.GeneralBorrowGrandchildSharedHistory
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshSharedSequence DuplicatePrefix.GeneralBorrowFreshReleaseMixed
open DuplicatePrefix.GeneralBorrowFreshMixedChild DuplicatePrefix.GeneralRangeMapOrigins
open DuplicatePrefix.GeneralBorrowPartitionState
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Actual root→child→grandchild shared generation from a recurring partition
state. Both structural Data records and the descendant's range ownership are
formed internally, including real append/reuse Slot choices. No successful
operation, generated-child graph or generated-child ownership is an input. -/
theorem generate (tree : BorrowTree) (root : UniIndex) (capacity : UInt64)
    (s : State tree root capacity) (firstTag secondTag : BorTag)
    (firstFresh : GeneralBorrowTagMap.Fresh tree.tagMapping firstTag)
    (secondFresh : GeneralBorrowTagMap.Fresh tree.tagMapping secondTag)
    (different : firstTag ≠ secondTag)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat)
    (room : tree.nodes.size+5 ≤ 4294967295) :
    ∃ first : Data tree firstTag root offset len,
    ∃ second : Data (child first {} false).tree secondTag (index first) offset len,
      index first ≠ root ∧ second.parentTag = firstTag ∧
      (read first {} false).status = .Completed ∧ (child first {} false).outcome = .ok () ∧
      (read second {} false).status = .Completed ∧ (child second {} false).outcome = .ok () ∧
      OwnedOn (Combined (child second {} false).tree {} (index second)
        (extend (extend (fun _ => true) (index first).toNat) (index second).toNat))
        offset (offset+len) (child second {} false).tree.locations ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin (child second {} false).tree (index second) .Read offset (offset+len) := by
  let first := GeneralBorrowChildSharedHistory.data tree root capacity s root s.node s.star.present firstTag firstFresh offset len nonzero bounds
  have initial : OwnedOn (Combined tree {} root (fun _ => true)) offset (offset+len) tree.locations := by
    intro position valid positive lower upper
    exact write_combined tree _ {} root (s.owned position valid)
  have generated := GeneralBorrowChildSharedHistory.child_owned tree root capacity s firstTag firstFresh offset len nonzero bounds
  let metadata := GeneralBorrowFreshStageMetadata.build tree firstTag root offset len first {} false (fun _ => true) initial
  have actual : child first {} false = GeneralBorrowPartitionSharedStage.operation tree s.node.tag firstTag offset len := by
    rfl
  have closed := GeneralBorrowPartitionSharedStage.borrow tree root capacity s offset len nonzero bounds firstTag firstFresh room
  obtain ⟨⟨next,tagged⟩⟩ := closed.2.2.1
  have state : State (child first {} false).tree root capacity := by rw [actual];exact next
  obtain ⟨node,present,taggedNode,exposed⟩ := metadata.node
  have freshNext : GeneralBorrowTagMap.Fresh (child first {} false).tree.tagMapping secondTag :=
    metadata.freshTag secondTag secondFresh different
  let second := GeneralBorrowChildSharedHistory.data (child first {} false).tree root capacity state (index first) node present secondTag freshNext offset len nonzero bounds
  have childReadOwned : OwnedOn (Combined (child first {} false).tree {} (index first)
      (extend (fun _ => true) (index first).toNat)) offset (offset+len) (child first {} false).tree.locations := generated.2.2.1
  have descended := GeneralBorrowFreshSharedSequence.run (child first {} false).tree secondTag (index first) offset len second {} false
    (extend (fun _ => true) (index first).toNat) childReadOwned
  have vacant : tree.nodes.get (index first) = none :=
    GeneralBorrowFreshSharedWithinStages.slot_vacant tree first.depth root first.slot
  have distinct : index first ≠ root := Ne.symm (GeneralBorrowFreshReuseNode.parent_not_vacant tree.nodes (index first) root s.node vacant s.star.present)
  have parentTag : second.parentTag = firstTag := taggedNode
  exact ⟨first,second,distinct,parentTag,generated.1,generated.2.1,descended.1,descended.2.1,descended.2.2.1,descended.2.2.2⟩

end DuplicatePrefix.GeneralBorrowGrandchildSharedHistory
