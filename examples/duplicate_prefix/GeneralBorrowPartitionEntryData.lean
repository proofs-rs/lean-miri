import duplicate_prefix.GeneralBorrowPartitionState
import duplicate_prefix.GenericAsMutPtrEntryValidity

namespace DuplicatePrefix.GeneralBorrowPartitionEntryData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGeneratedStarShape DuplicatePrefix.GeneralBorrowSharedGeneratorProfile
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Form real retag-entry Data from a sparse star, including arbitrary reusable
free slots. The actual selected append/reuse Slot is constructed from Pool and
Accounting; its success is not assumed. -/
noncomputable def data (tree : BorrowTree) (root : UniIndex) (capacity : UInt64)
    (s : GeneralBorrowPartitionState.State tree root capacity)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) :
    GenericAsMutPtrEntryValidity.Data tree {} s.node.tag tag 0 capacity := by
  let node := s.node
  have star := s.star
  have roots := s.roots
  have allocator := s.allocator
  have room := s.room
  let depth := GeneralBorrowStarCertificates.depth tree root node star
  have fit : tree.nodes.size ≤ 4294967296 := by omega
  have positive := GeneralBorrowNodeUpdate.lookup_valid tree.nodes root node star.present
  have slack : depth.depth root < tree.nodes.size := by
    have available : 0 < tree.nodes.data.size := by omega
    simpa [depth,GeneralBorrowStarCertificates.depth,UniValMap.size] using available
  have aligned := GeneralBorrowFreshStagePool.empty_aligned tree allocator.accounting
  have bounds : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size ≤ 4294967295 := by
    intro empty
    rw [aligned empty]
    change tree.nodes.size ≤ 4294967295
    omega
  exact {
    parent := root,root := root,node := node,depth := depth
    children := GeneralBorrowStarCertificates.children tree root node star
    parentPresent := star.present,roots := roots
    covered := GeneralBorrowStarCertificates.covered tree root node star roots
    tagPresent := allocator.nodeTags root node star.present
    tagFresh := fresh
    protectorFresh := GeneralBorrowFullSharedResources.protector_fresh tree allocator.nodeTags tag fresh
    nodeFits := fit
    slot := GeneralBorrowFreshAllocatorInvariant.slot tree depth root allocator.pool aligned bounds slack
    well := s.well
    owned := by
      intro position valid _ _ _
      exact s.owned position valid }

end DuplicatePrefix.GeneralBorrowPartitionEntryData
