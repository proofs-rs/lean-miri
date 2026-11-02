import duplicate_prefix.GeneralBorrowReusableStar
import duplicate_prefix.GeneralBorrowRangeProperty

namespace DuplicatePrefix.GeneralBorrowPartitionState
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGeneratedStarShape DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

set_option autoImplicit false in
/-- A recurring state whose locations may be partitioned and have different
permissions. Write ownership belongs to the root; foreign states may be Disabled. -/
structure State (tree : BorrowTree) (root : UniIndex) (bytes : UInt64) where
  node : TreeNode
  nonzero : bytes ≠ 0
  star : Star tree root node
  roots : tree.roots = #[root]
  capacity : tree.locations.size = Size.ofBytes bytes
  well : tree.locations.WellFormed
  owned : Every (GeneralBorrowRange.LocationOwned tree {} root .Write) tree.locations
  allocator : GeneralBorrowGcAllocator.Invariant tree
  clean : GeneralBorrowGcVacantClean.VacantClean tree
  room : tree.nodes.size+4 ≤ 4294967295

/-- Every generated mixed shared/GC state supplies partition ownership before
any subrange accesses. No new permission or graph assumption is introduced. -/
def of_reusable (tree : BorrowTree) (root : UniIndex) (bytes : UInt64)
    (s : GeneralBorrowReusableStar.State tree root bytes) : State tree root bytes where
  node := s.node
  nonzero := s.nonzero
  star := s.star
  roots := s.roots
  capacity := by rw [s.locations];simp [RangeMapNonempty.homogeneous,DedupRangeMap.size,Size.ofBytes]
  well := by rw [s.locations];simp [RangeMapNonempty.homogeneous,DedupRangeMap.WellFormed,UInt64.pos_iff_ne_zero.mpr s.nonzero]
  owned := by
    rw [s.locations]
    intro position valid
    have zero : position = 0 := by change position < 1 at valid;omega
    subst position
    exact GeneralBorrowStarOwnership.location_owned tree root s.node s.star s.location s.profile (by have bound := s.room;omega)
  allocator := s.allocator
  clean := by
    intro query vacant position valid
    rw [s.locations] at valid
    have zero : position = 0 := by change position < 1 at valid;omega
    subst position
    simpa only [s.locations,RangeMapNonempty.homogeneous,Array.getElem_singleton] using s.profile.vacant query vacant
  room := s.room

def operation (tree : BorrowTree) (tag : BorTag) (offset len : UInt64) (kind : AccessKind) :=
  tree.performNormalAccessRange tag (Size.ofBytes offset) (Size.ofBytes len) kind {} .VisitChildrenOfAccessed

/-- Any in-bounds subrange Read or Write completes and forms another partition
state. The actual interval preparation/splits and write-back are included. -/
theorem access (tree : BorrowTree) (root : UniIndex) (bytes : UInt64)
    (s : State tree root bytes) (offset len : UInt64) (kind : AccessKind)
    (bounds : offset.toNat+len.toNat ≤ bytes.toNat) :
    (operation tree s.node.tag offset len kind).status = .Completed ∧
    Nonempty {post : State (operation tree s.node.tag offset len kind).tree root bytes // post.node.tag = s.node.tag} ∧
    (operation tree s.node.tag offset len kind).tree.nodes.size = tree.nodes.size ∧
    (operation tree s.node.tag offset len kind).tree.tagMapping = tree.tagMapping := by
  let depth := GeneralBorrowStarCertificates.depth tree root s.node s.star
  have children := GeneralBorrowStarCertificates.children tree root s.node s.star
  have covered := GeneralBorrowStarCertificates.covered tree root s.node s.star s.roots
  have fits : tree.nodes.data.size ≤ 4294967296 := by have room := s.room;change tree.nodes.data.size+4 ≤ _ at room;omega
  have request : (Size.ofBytes offset).bytes.toNat+(Size.ofBytes len).bytes.toNat ≤ tree.locations.size.bytes.toNat := by
    rw [s.capacity];exact bounds
  have tagged := s.allocator.nodeTags root s.node s.star.present
  have facts := GeneralBorrowRangePreserves.ranged tree {} s.node.tag root root (Size.ofBytes offset) (Size.ofBytes len)
    kind .Write .VisitChildrenOfAccessed (by intro impossible;cases impossible) fits depth children s.node s.star.present
    s.roots covered tagged s.well s.owned request
  let predicate := fun location : LocationTree => ∀ query, tree.nodes.get query = none → location.perms.get query = none
  have initial : Every predicate tree.locations := by
    intro position valid query vacant
    exact s.clean query vacant position valid
  have preserved := GeneralBorrowRangeProperty.preserves predicate tree {} s.node.tag root root (Size.ofBytes offset) (Size.ofBytes len)
    kind .Write .VisitChildrenOfAccessed (by intro impossible;cases impossible) fits depth children s.node s.star.present
    s.roots covered tagged s.well s.owned initial (by
      intro location good owned query vacant
      exact GeneralBorrowFreshActiveOnClean.normal_vacant tree location {} root query kind .VisitChildrenOfAccessed
        depth children s.node s.star.present vacant (good query vacant)) request
  have frame := GeneralBorrowFreshReadFrame.frame tree (.concrete s.node.tag) (Size.ofBytes offset) (Size.ofBytes len)
    kind {} .VisitChildrenOfAccessed
  have nodes : (operation tree s.node.tag offset len kind).tree.nodes = tree.nodes := by simpa only [operation,BorrowTree.performNormalAccessRange] using congrArg BorrowTree.nodes frame
  have mapping : (operation tree s.node.tag offset len kind).tree.tagMapping = tree.tagMapping := by simpa only [operation,BorrowTree.performNormalAccessRange] using congrArg BorrowTree.tagMapping frame
  have roots : (operation tree s.node.tag offset len kind).tree.roots = tree.roots := by simpa only [operation,BorrowTree.performNormalAccessRange] using congrArg BorrowTree.roots frame
  have clean : GeneralBorrowGcVacantClean.VacantClean (operation tree s.node.tag offset len kind).tree := by
    intro query vacant position valid
    rw [nodes] at vacant
    exact preserved.2.1 position valid query vacant
  refine ⟨facts.1,⟨⟨⟨s.node,s.nonzero,of_nodes tree _ root s.node nodes s.star,roots.trans s.roots,
    facts.2.2.2.trans s.capacity,facts.2.2.1,facts.2.1,?_,clean,?_⟩,rfl⟩⟩,congrArg UniValMap.size nodes,mapping⟩
  · constructor
    · simpa only [nodes,mapping] using s.allocator.pool
    · simpa only [GeneralBorrowFreshStagePool.Accounting,nodes,mapping] using s.allocator.accounting
    · simpa only [mapping] using s.allocator.unique
    · intro query node present
      rw [nodes] at present
      rw [mapping]
      exact s.allocator.nodeTags query node present
  · rw [nodes];exact s.room

end DuplicatePrefix.GeneralBorrowPartitionState
