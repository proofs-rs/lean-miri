import duplicate_prefix.GeneralBorrowReusableStar
import duplicate_prefix.GeneralBorrowStarRead

namespace DuplicatePrefix.GeneralBorrowReusableRead
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowReusableStar
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def operation (tree : BorrowTree) (tag : BorTag) (capacity : UInt64) :=
  tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes 0) (Size.ofBytes capacity)
    .Read {} .VisitChildrenOfAccessed

/-- A real root Read on the reusable sparse state completes, retaining the
root tag, all allocator data, and exact permissions including vacant Clean. -/
theorem complete (tree : BorrowTree) (root : UniIndex) (capacity : UInt64)
    (s : State tree root capacity) :
    (operation tree s.node.tag capacity).status = .Completed ∧
    Nonempty {post : State (operation tree s.node.tag capacity).tree root capacity // post.node.tag = s.node.tag} ∧
    (operation tree s.node.tag capacity).tree.nodes.size = tree.nodes.size ∧
    (operation tree s.node.tag capacity).tree.tagMapping = tree.tagMapping := by
  have fit : tree.nodes.size ≤ 4294967296 := by have bound := s.room;omega
  have facts := GeneralBorrowStarRead.complete tree root s.node s.star s.roots s.node.tag
    (s.allocator.nodeTags root s.node s.star.present) capacity s.nonzero s.location s.locations s.profile fit
  let location := (tree.performNormalAccessAt s.location root .Read {} .VisitChildrenOfAccessed).location
  have exactTree : (operation tree s.node.tag capacity).tree =
      {tree with locations := RangeMapNonempty.homogeneous capacity location} := facts.2.1
  refine ⟨facts.1,?_,?_,?_⟩
  · rw [exactTree]
    have profile : GeneralBorrowSharedGeneratorProfile.Profile
        {tree with locations := RangeMapNonempty.homogeneous capacity location} location root := by
      have known := facts.2.2
      change GeneralBorrowSharedGeneratorProfile.Profile (operation tree s.node.tag capacity).tree location root at known
      rw [exactTree] at known
      exact known
    exact ⟨⟨⟨s.node,location,s.nonzero,GeneralBorrowGeneratedStarShape.locations tree root s.node s.star _,
      s.roots,rfl,profile,
      ⟨s.allocator.pool,s.allocator.accounting,s.allocator.unique,s.allocator.nodeTags⟩,s.room⟩,rfl⟩⟩
  · rw [exactTree]
  · rw [exactTree]

/-- Keeping the distinguished tag live makes the fixed-tag interface available
for the next operation, even after arbitrary deletions of shared leaves. -/
theorem collect (tree : BorrowTree) (root : UniIndex) (capacity : UInt64)
    (s : State tree root capacity) (extraLive : Array BorTag) :
    let result := tree.removeUnreachableTags (#[s.node.tag] ++ extraLive)
    result.outcome = .ok () ∧
    Nonempty {post : State result.tree root capacity // post.node.tag = s.node.tag} ∧
    result.tree.nodes.size = tree.nodes.size ∧
    (∀ tag, GeneralBorrowTagMap.Fresh tree.tagMapping tag → GeneralBorrowTagMap.Fresh result.tree.tagMapping tag) := by
  dsimp only
  have completed := GeneralBorrowReusableStar.collect tree root capacity s (#[s.node.tag] ++ extraLive)
  obtain ⟨post⟩ := completed.2
  have retained := GeneralBorrowGcLiveNode.preserves tree root s.node.tag (#[s.node.tag] ++ extraLive)
    (by simp) ⟨s.node,s.star.present,rfl⟩
  obtain ⟨node,present,tagged⟩ := retained
  have same : post.node = node := Option.some.inj (post.star.present.symm.trans present)
  have frame := GeneralBorrowGcResourceFrame.preserves (fun i : Fin 0 => Fin.elim0 i) tree
    (#[s.node.tag] ++ extraLive) (by intro i;exact Fin.elim0 i)
  refine ⟨completed.1,⟨⟨post,same ▸ tagged⟩⟩,frame.capacity,?_⟩
  intro tag fresh
  exact (GeneralBorrowGcResourceFrame.preserves (fun _ : Fin 1 => tag) tree
    (#[s.node.tag] ++ extraLive) (fun _ => fresh)).fresh 0

end DuplicatePrefix.GeneralBorrowReusableRead
