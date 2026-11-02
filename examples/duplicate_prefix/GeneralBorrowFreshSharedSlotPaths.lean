import duplicate_prefix.GeneralBorrowFreshMetadataChildSlot
import duplicate_prefix.GeneralBorrowFreshSharedPaths

namespace DuplicatePrefix.GeneralBorrowFreshSharedSlotPaths
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
    (isProtected : Bool) (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (oldLocation newLocation : LocationTree) (protections : ProtectedTags)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree oldLocation protections).topology) :
    GeneralBorrowFreshSharedPaths.Attach (source_normal_projection tree oldLocation protections).topology
      (source_normal_projection (GeneralBorrowFreshMetadataChildSlot.result tree parentTag newTag isProtected offset len) newLocation protections).topology
      parent.toNat (GeneralBorrowFreshMetadataChildSlot.index slot).toNat := by
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildShared.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,fresh,
        noFree,aligned,fits,isProtected,offset,len,nonzero,well,bounds⟩
    have extension := (GeneralBorrowFreshMetadataChildShared.append input).extension oldLocation newLocation protections
    have actual := GeneralBorrowFreshSharedPaths.of_append _ _ parent.toNat extension forest
    have projectedSize : (source_normal_projection tree oldLocation protections).topology.nodes.size = tree.nodes.data.size := by
      unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
    have atEnd : (GeneralBorrowFreshMetadataChildShared.index input).toNat = tree.nodes.data.size :=
      GeneralBorrowFreshMetadataChildShared.at_end input
    rw [projectedSize,←atEnd] at actual
    exact actual
  | reuse index available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildSharedReuse.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,fresh,
        index,available,bounded,vacant,slack,isProtected,offset,len,nonzero,well,bounds⟩
    have extension := (GeneralBorrowFreshMetadataChildSharedReuse.reuse input).extension oldLocation newLocation protections
    exact GeneralBorrowFreshSharedPaths.of_reuse _ _ index.toNat parent.toNat extension forest

end DuplicatePrefix.GeneralBorrowFreshSharedSlotPaths
