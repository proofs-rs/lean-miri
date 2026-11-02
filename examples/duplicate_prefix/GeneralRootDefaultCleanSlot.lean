import duplicate_prefix.GeneralBorrowFreshMetadataChildDefaultSlot
import duplicate_prefix.GeneralBorrowFreshMetadataChildProtector
import duplicate_prefix.GeneralBorrowFreshMetadataChildAllocator
import duplicate_prefix.GeneralBorrowFreshFutureClean
namespace DuplicatePrefix.GeneralRootDefaultCleanSlot
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshReadFrame GeneralBorrowFreshReborrowStages
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

set_option autoImplicit false in
theorem mutable_slot
    (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (children : GeneralBorrowGraph.ChildNodes tree) (covered : GeneralBorrowGraph.RootsCover tree)
    (parentTag newTag : BorTag) (parent : UniIndex) (node : TreeNode)
    (tagPresent : tree.tagMapping.get parentTag = some parent) (parentPresent : tree.nodeAt parent = some node)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (slot : Slot tree depth parent)
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (query : UniIndex) (different : query ≠ GeneralBorrowFreshMetadataChildDefaultSlot.index slot)
    (clean : GeneralBorrowFreshFutureClean.Clean tree query) :
    GeneralBorrowFreshFutureClean.Clean
      (GeneralBorrowFreshMetadataChildDefaultSlot.result tree parentTag newTag offset len) query := by
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildDefault.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,node,tagPresent,parentPresent,fresh,
        noFree,aligned,fits,offset,len,nonzero,well,bounds⟩
    have modified := GeneralBorrowFreshFutureClean.modified tree.locations (GeneralBorrowFreshMetadataChildDefault.index input) query
      (Size.ofBytes offset) (Size.ofBytes len) GeneralBorrowFreshDefaultChild.inside different well bounds clean
    have stageClean : GeneralBorrowFreshFutureClean.Clean (GeneralBorrowFreshMetadataChildDefault.stage input) query := modified
    exact GeneralBorrowFreshFutureClean.shape_preserves _ _ (GeneralBorrowFreshMetadataChildDefault.shape input) query stageClean
  | reuse index available valid vacant slack =>
    let input : GeneralBorrowFreshMetadataChildDefaultReuse.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,node,tagPresent,parentPresent,fresh,
        index,available,valid,vacant,slack,offset,len,nonzero,well,bounds⟩
    have modified := GeneralBorrowFreshFutureClean.modified tree.locations index query
      (Size.ofBytes offset) (Size.ofBytes len) GeneralBorrowFreshDefaultChild.inside different well bounds clean
    have stageClean : GeneralBorrowFreshFutureClean.Clean (GeneralBorrowFreshMetadataChildDefaultReuse.stage input) query := modified
    exact GeneralBorrowFreshFutureClean.shape_preserves _ _ (GeneralBorrowFreshMetadataChildDefaultReuse.shape input) query stageClean

end DuplicatePrefix.GeneralRootDefaultCleanSlot
