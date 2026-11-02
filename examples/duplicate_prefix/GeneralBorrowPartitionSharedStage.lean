import duplicate_prefix.GeneralBorrowPartitionShared

namespace DuplicatePrefix.GeneralBorrowPartitionSharedStage
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowPartitionState
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- The actual root Read followed by the partial-range shared constructor. -/
def operation (tree : BorrowTree) (parentTag tag : BorTag) (offset len : UInt64) :=
  GeneralBorrowPartitionShared.operation (GeneralBorrowPartitionState.operation tree parentTag offset len .Read).tree parentTag tag offset len

/-- A complete actual partial-range shared stage forms the next recurring
partition state. Both operation successes and every reused-slot condition are
conclusions; numeric capacity and unused tags are explicit resources. -/
theorem borrow (tree : BorrowTree) (root : UniIndex) (capacity : UInt64)
    (s : State tree root capacity) (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (room : tree.nodes.size+5 ≤ 4294967295) :
    (GeneralBorrowPartitionState.operation tree s.node.tag offset len .Read).status = .Completed ∧
    (operation tree s.node.tag tag offset len).outcome = .ok () ∧
    Nonempty {post : State (operation tree s.node.tag tag offset len).tree root capacity // post.node.tag = s.node.tag} ∧
    (operation tree s.node.tag tag offset len).tree.nodes.size ≤ tree.nodes.size+1 ∧
    (∀ future, tag ≠ future → GeneralBorrowTagMap.Fresh tree.tagMapping future →
      GeneralBorrowTagMap.Fresh (operation tree s.node.tag tag offset len).tree.tagMapping future) := by
  have read := GeneralBorrowPartitionState.access tree root capacity s offset len .Read bounds
  obtain ⟨⟨prepared,tagged⟩⟩ := read.2.1
  have preparedFresh : GeneralBorrowTagMap.Fresh (GeneralBorrowPartitionState.operation tree s.node.tag offset len .Read).tree.tagMapping tag := by
    rw [read.2.2.2];exact fresh
  have preparedRoom : (GeneralBorrowPartitionState.operation tree s.node.tag offset len .Read).tree.nodes.size+5 ≤ 4294967295 := by
    rw [read.2.2.1];exact room
  have child := GeneralBorrowPartitionShared.shared _ root capacity prepared offset len nonzero bounds tag preparedFresh preparedRoom
  rw [tagged] at child
  refine ⟨read.1,child.1,child.2.1,?_,?_⟩
  · have bound := child.2.2.1
    rw [read.2.2.1] at bound
    exact bound
  · intro future different unused
    exact child.2.2.2 future different (by rw [read.2.2.2];exact unused)

end DuplicatePrefix.GeneralBorrowPartitionSharedStage
