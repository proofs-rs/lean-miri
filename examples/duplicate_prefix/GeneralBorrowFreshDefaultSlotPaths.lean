import duplicate_prefix.GeneralBorrowFreshMetadataChildDefaultSlot
import duplicate_prefix.GeneralBorrowFreshSharedPaths

namespace DuplicatePrefix.GeneralBorrowFreshDefaultSlotPaths
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowFreshReborrowStages (Slot)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Actual append OR vacant-slot reuse supplies full ancestor attachment,
including production traversal-fuel changes. Only initial forest/allocator
metadata is supplied; no constructor success or poststate graph is assumed. -/
theorem attach (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (children : GeneralBorrowGraph.ChildNodes tree) (covered : GeneralBorrowGraph.RootsCover tree)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (parentTagPresent : tree.indexOfTag parentTag = some parent) (parentPresent : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (slot : Slot tree depth parent)
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (oldLocation newLocation : LocationTree) (protections : ProtectedTags)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree oldLocation protections).topology) :
    GeneralBorrowFreshSharedPaths.Attach (source_normal_projection tree oldLocation protections).topology
      (source_normal_projection (GeneralBorrowFreshMetadataChildDefaultSlot.result tree parentTag newTag offset len) newLocation protections).topology
      parent.toNat (GeneralBorrowFreshMetadataChildDefaultSlot.index slot).toNat := by
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildDefault.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,fresh,
        noFree,aligned,fits,offset,len,nonzero,well,bounds⟩
    have extension := (GeneralBorrowFreshMetadataChildDefault.append input).extension oldLocation newLocation protections
    have actual := GeneralBorrowFreshSharedPaths.of_append _ _ parent.toNat extension forest
    have projectedSize : (source_normal_projection tree oldLocation protections).topology.nodes.size = tree.nodes.data.size := by
      unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
    have atEnd : (GeneralBorrowFreshMetadataChildDefault.index input).toNat = tree.nodes.data.size :=
      GeneralBorrowFreshMetadataChildDefault.at_end input
    rw [projectedSize,←atEnd] at actual
    exact actual
  | reuse index available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildDefaultReuse.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,fresh,
        index,available,bounded,vacant,slack,offset,len,nonzero,well,bounds⟩
    have extension := (GeneralBorrowFreshMetadataChildDefaultReuse.reuse input).extension oldLocation newLocation protections
    exact GeneralBorrowFreshSharedPaths.of_reuse _ _ index.toNat parent.toNat extension forest

end DuplicatePrefix.GeneralBorrowFreshDefaultSlotPaths
