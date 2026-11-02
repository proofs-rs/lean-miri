import duplicate_prefix.GeneralBorrowRetainedMutableReborrow
namespace DuplicatePrefix.GeneralBorrowRetainedMutableReborrowFacts
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowRetainedMutableAccess GeneralBorrowRetainedMutableReborrow
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

theorem oldLookup {root child : UniIndex} {childTag : BorTag} {offset len : UInt64}
    (s : State root child childTag offset len) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh s.tree.tagMapping tag) (nonzero : len≠0)
    (room : s.tree.nodes.size+5≤4294967295) (future : BorTag) (different : tag≠future) :
    (GeneralBorrowRetainedMutableReborrow.build s tag fresh nonzero room).state.tree.indexOfTag future=s.tree.indexOfTag future := by
  rw [(GeneralBorrowRetainedMutableReborrow.build s tag fresh nonzero room).actual]
  exact (GeneralBorrowSharedRootMutableReservation.build s.tree tag child offset len (data s tag fresh nonzero)
    s.owned s.resources.allocator s.resources.clean).oldLookup future different

theorem size {root child : UniIndex} {childTag : BorTag} {offset len : UInt64}
    (s : State root child childTag offset len) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh s.tree.tagMapping tag) (nonzero : len≠0)
    (room : s.tree.nodes.size+5≤4294967295) :
    (GeneralBorrowRetainedMutableReborrow.build s tag fresh nonzero room).state.tree.nodes.size≤s.tree.nodes.size+1 := by
  rw [(GeneralBorrowRetainedMutableReborrow.build s tag fresh nonzero room).actual]
  exact (GeneralBorrowSharedRootMutableReservation.build s.tree tag child offset len (data s tag fresh nonzero)
    s.owned s.resources.allocator s.resources.clean).size

theorem fresh {root child : UniIndex} {childTag : BorTag} {offset len : UInt64}
    (s : State root child childTag offset len) (tag : BorTag)
    (unused : GeneralBorrowTagMap.Fresh s.tree.tagMapping tag) (nonzero : len≠0)
    (room : s.tree.nodes.size+5≤4294967295) (future : BorTag)
    (futureFresh : GeneralBorrowTagMap.Fresh s.tree.tagMapping future) (different : tag≠future) :
    GeneralBorrowTagMap.Fresh (GeneralBorrowRetainedMutableReborrow.build s tag unused nonzero room).state.tree.tagMapping future := by
  apply GeneralBorrowForestForeignSharedFresh.fresh_of_absent
  change (GeneralBorrowRetainedMutableReborrow.build s tag unused nonzero room).state.tree.indexOfTag future=none
  rw [oldLookup s tag unused nonzero room future different]
  unfold BorrowTree.indexOfTag UniKeyMap.get
  rw [GeneralBorrowTagMap.fresh_find s.tree.tagMapping future futureFresh]
  rfl
end
end DuplicatePrefix.GeneralBorrowRetainedMutableReborrowFacts
