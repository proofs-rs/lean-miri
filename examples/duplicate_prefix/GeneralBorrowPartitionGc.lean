import duplicate_prefix.GeneralBorrowGcPartitionOwnership
import duplicate_prefix.GeneralBorrowGcPartitionComplete

namespace DuplicatePrefix.GeneralBorrowPartitionGc
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowPartitionState
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Real collection retains the current root and any additional live tags. -/
def operation (tree : BorrowTree) (rootTag : BorTag) (extraLive : Array BorTag) :=
  tree.removeUnreachableTags (#[rootTag] ++ extraLive)

/-- Full production GC on a partitioned state completes and re-establishes all
recurring graph/ownership/allocator/Clean resources. No homogeneous map, completed
GC, resulting permission state or operation trace is an input. -/
theorem collect (tree : BorrowTree) (root : UniIndex) (bytes : UInt64)
    (s : State tree root bytes) (extraLive : Array BorTag) :
    (operation tree s.node.tag extraLive).outcome = .ok () ∧
    Nonempty {post : State (operation tree s.node.tag extraLive).tree root bytes // post.node.tag = s.node.tag} ∧
    (operation tree s.node.tag extraLive).tree.nodes.size = tree.nodes.size ∧
    (∀ tag, GeneralBorrowTagMap.Fresh tree.tagMapping tag →
      GeneralBorrowTagMap.Fresh (operation tree s.node.tag extraLive).tree.tagMapping tag) := by
  let live := #[s.node.tag] ++ extraLive
  have completed := GeneralBorrowGcPartitionComplete.complete tree root s.node live s.star s.roots s.well
  obtain ⟨node,star⟩ := GeneralBorrowGcStarShape.preserves tree root s.node live s.star s.roots
  have frame := GeneralBorrowGcResourceFrame.preserves (fun i : Fin 0 => Fin.elim0 i) tree live (by intro i;exact Fin.elim0 i)
  have policy := GeneralBorrowGcEffectivePolicy.preserves (GeneralBorrowGcPartitionOwnership.Allowed root) tree root s.node live s.star s.roots
    (GeneralBorrowGcPartitionOwnership.of_state tree root bytes s)
  have capacity : (operation tree s.node.tag extraLive).tree.nodes.size = tree.nodes.size := by
    simpa only [operation,live] using frame.capacity
  have fits : (operation tree s.node.tag extraLive).tree.nodes.size ≤ 4294967296 := by
    rw [capacity];have bound := s.room;omega
  have owned := GeneralBorrowGcPartitionOwnership.ownership (operation tree s.node.tag extraLive).tree root node star policy fits
  have retained := GeneralBorrowGcLiveNode.preserves tree root s.node.tag live (by simp [live]) ⟨s.node,s.star.present,rfl⟩
  obtain ⟨other,present,tagged⟩ := retained
  have same : node = other := Option.some.inj (star.present.symm.trans present)
  refine ⟨completed.1,⟨⟨⟨node,s.nonzero,star,frame.roots.trans s.roots,completed.2.2.trans s.capacity,
    completed.2.1,owned,GeneralBorrowGcAllocatorFull.preserves tree live s.allocator,policy.vacant,?_⟩,same ▸ tagged⟩⟩,frame.capacity,?_⟩
  · rw [capacity];exact s.room
  · intro tag fresh
    exact (GeneralBorrowGcResourceFrame.preserves (fun _ : Fin 1 => tag) tree live (fun _ => fresh)).fresh 0

end DuplicatePrefix.GeneralBorrowPartitionGc
