import duplicate_prefix.GeneralBorrowProtectedMutableStage
namespace DuplicatePrefix.GeneralBorrowProtectedRootRead
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowPartitionState DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def operation (tree : BorrowTree) (parentTag : BorTag) (offset len : UInt64) (tag : BorTag) :=
  tree.performNormalAccessRange parentTag (Size.ofBytes offset) (Size.ofBytes len) .Read
    (({} : ProtectedTags).insert tag .StrongProtector) .VisitChildrenOfAccessed

/-- A real Read with a fresh singleton registration preserves a counterfactual
unheld root State, before the child bearing that tag has been installed. -/
theorem read (tree : BorrowTree) (root : UniIndex) (bytes : UInt64)
    (s : State tree root bytes) (offset len : UInt64) (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (bounds : offset.toNat+len.toNat ≤ bytes.toNat) :
    (operation tree s.node.tag offset len tag).status = .Completed ∧
    Nonempty {post : State (operation tree s.node.tag offset len tag).tree root bytes // post.node.tag = s.node.tag} ∧
    (operation tree s.node.tag offset len tag).tree.nodes.size = tree.nodes.size ∧
    (operation tree s.node.tag offset len tag).tree.tagMapping = tree.tagMapping := by
  let protections := ({} : ProtectedTags).insert tag .StrongProtector
  let entry := GeneralBorrowPartitionEntryData.data tree root bytes s tag fresh
  have owners := GeneralBorrowProtector.range_owned tree {} tag .StrongProtector entry.protectorFresh root .Write s.owned
  let depth := GeneralBorrowStarCertificates.depth tree root s.node s.star
  have children := GeneralBorrowStarCertificates.children tree root s.node s.star
  have covered := GeneralBorrowStarCertificates.covered tree root s.node s.star s.roots
  have fits : tree.nodes.data.size ≤ 4294967296 := by have room := s.room;change tree.nodes.data.size+4 ≤ _ at room;omega
  have request : (Size.ofBytes offset).bytes.toNat+(Size.ofBytes len).bytes.toNat ≤ tree.locations.size.bytes.toNat := by
    rw [s.capacity];exact bounds
  have tagged := s.allocator.nodeTags root s.node s.star.present
  have facts := GeneralBorrowRangePreserves.ranged tree protections s.node.tag root root (Size.ofBytes offset) (Size.ofBytes len)
    .Read .Write .VisitChildrenOfAccessed (by intro impossible;cases impossible) fits depth children s.node s.star.present
    s.roots covered tagged s.well owners request
  let predicate := fun location : LocationTree => ∀ query, tree.nodes.get query = none → location.perms.get query = none
  have initial : Every predicate tree.locations := by
    intro position valid query vacant
    exact s.clean query vacant position valid
  have preserved := GeneralBorrowRangeProperty.preserves predicate tree protections s.node.tag root root (Size.ofBytes offset) (Size.ofBytes len)
    .Read .Write .VisitChildrenOfAccessed (by intro impossible;cases impossible) fits depth children s.node s.star.present
    s.roots covered tagged s.well owners initial (by
      intro location good owned query vacant
      exact GeneralBorrowFreshActiveOnClean.normal_vacant tree location protections root query .Read .VisitChildrenOfAccessed
        depth children s.node s.star.present vacant (good query vacant)) request
  have frame := GeneralBorrowFreshReadFrame.frame tree (.concrete s.node.tag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read protections .VisitChildrenOfAccessed
  have nodes : (operation tree s.node.tag offset len tag).tree.nodes = tree.nodes := by simpa only [operation,BorrowTree.performNormalAccessRange] using congrArg BorrowTree.nodes frame
  have mapping : (operation tree s.node.tag offset len tag).tree.tagMapping = tree.tagMapping := by simpa only [operation,BorrowTree.performNormalAccessRange] using congrArg BorrowTree.tagMapping frame
  have roots : (operation tree s.node.tag offset len tag).tree.roots = tree.roots := by simpa only [operation,BorrowTree.performNormalAccessRange] using congrArg BorrowTree.roots frame
  have clean : GeneralBorrowGcVacantClean.VacantClean (operation tree s.node.tag offset len tag).tree := by
    intro query vacant position valid
    rw [nodes] at vacant
    exact preserved.2.1 position valid query vacant
  refine ⟨facts.1,⟨⟨⟨s.node,s.nonzero,GeneralBorrowGeneratedStarShape.of_nodes tree _ root s.node nodes s.star,roots.trans s.roots,
    facts.2.2.2.trans s.capacity,facts.2.2.1,?_,?_,clean,?_⟩,rfl⟩⟩,congrArg UniValMap.size nodes,mapping⟩
  · intro position valid
    exact GeneralBorrowFreshProtectorRelease.location_weakens _ _ protections {} (by intro tag impossible; simp [ProtectedTags.contains,ProtectedTags.get] at impossible)
      root .Write (facts.2.1 position valid)
  · constructor
    · simpa only [nodes,mapping] using s.allocator.pool
    · simpa only [GeneralBorrowFreshStagePool.Accounting,nodes,mapping] using s.allocator.accounting
    · simpa only [mapping] using s.allocator.unique
    · intro query node present
      rw [nodes] at present
      rw [mapping]
      exact s.allocator.nodeTags query node present
  · rw [nodes];exact s.room

end DuplicatePrefix.GeneralBorrowProtectedRootRead
