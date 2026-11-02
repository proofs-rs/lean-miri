import duplicate_prefix.GeneralBorrowZeroSharedState

namespace DuplicatePrefix.GeneralBorrowZeroSharedStage
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowPartitionState
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

/-- A genuine empty-range root Read followed by genuine empty-range shared
construction. The new child remains a real lazy Frozen node. -/
def operation (tree : BorrowTree) (parentTag tag : BorTag) (offset : UInt64) :=
  GeneralBorrowZeroSharedState.operation
    (GeneralBorrowPartitionState.operation tree parentTag offset 0 .Read).tree parentTag tag offset

/-- Both real operations complete and produce the next recurring state,
without a successful-operation or resulting ownership premise. The raw
constructor requires no bounds, but the preceding Read's bounds remain explicit. -/
theorem borrow (tree : BorrowTree) (root : UniIndex) (bytes : UInt64) (s : State tree root bytes)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (room : tree.nodes.size+5 ≤ 4294967295) (offset : UInt64) (bounds : offset.toNat ≤ bytes.toNat) :
    (GeneralBorrowPartitionState.operation tree s.node.tag offset 0 .Read).status = .Completed ∧
    (operation tree s.node.tag tag offset).outcome = .ok () ∧
    Nonempty {post : State (operation tree s.node.tag tag offset).tree root bytes // post.node.tag = s.node.tag} ∧
    (operation tree s.node.tag tag offset).tree.nodes.size ≤ tree.nodes.size+1 ∧
    (∀ future, tag ≠ future → GeneralBorrowTagMap.Fresh tree.tagMapping future →
      GeneralBorrowTagMap.Fresh (operation tree s.node.tag tag offset).tree.tagMapping future) := by
  have read := GeneralBorrowPartitionState.access tree root bytes s offset 0 .Read (by simpa using bounds)
  obtain ⟨⟨prepared,tagged⟩⟩ := read.2.1
  have readyFresh : GeneralBorrowTagMap.Fresh (GeneralBorrowPartitionState.operation tree s.node.tag offset 0 .Read).tree.tagMapping tag := by
    rw [read.2.2.2];exact fresh
  have readyRoom : (GeneralBorrowPartitionState.operation tree s.node.tag offset 0 .Read).tree.nodes.size+5 ≤ 4294967295 := by
    rw [read.2.2.1];exact room
  have constructed := GeneralBorrowZeroSharedState.shared _ root bytes prepared tag readyFresh readyRoom offset
  rw [tagged] at constructed
  refine ⟨read.1,constructed.1,constructed.2.1,?_,?_⟩
  · have bound := constructed.2.2.1
    rw [read.2.2.1] at bound
    exact bound
  · intro future different unused
    exact constructed.2.2.2 future different (by rw [read.2.2.2];exact unused)

end DuplicatePrefix.GeneralBorrowZeroSharedStage
