import duplicate_prefix.GeneralBorrowFreshMetadataChildDefaultSlot
import duplicate_prefix.GeneralBorrowFreshMetadataChildProtector
import duplicate_prefix.GeneralBorrowFreshMetadataChildAllocator
import duplicate_prefix.GeneralBorrowFreshFutureClean
namespace DuplicatePrefix.GeneralRootDefaultFreshSlot
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
    (next : BorTag) (nodeFresh : GeneralBorrowProtector.Fresh tree next) (different : newTag ≠ next) :
    let after := GeneralBorrowFreshMetadataChildDefaultSlot.result tree parentTag newTag offset len
    (GeneralBorrowTagMap.Fresh tree.tagMapping next → GeneralBorrowTagMap.Fresh after.tagMapping next) ∧ GeneralBorrowProtector.Fresh after next := by
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildDefault.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,node,tagPresent,parentPresent,fresh,
        noFree,aligned,fits,offset,len,nonzero,well,bounds⟩
    constructor
    · intro mapFresh
      change GeneralBorrowTagMap.Fresh (GeneralBorrowFreshMetadataChildDefault.result input).tagMapping next
      rw [(GeneralBorrowFreshMetadataChildDefault.append input).mapping]
      exact GeneralBorrowFreshMetadataChildAllocator.fresh_push tree.tagMapping newTag next _ _ mapFresh different
    · apply GeneralBorrowFreshMetadataChildProtector.of_shape _ _ (GeneralBorrowFreshMetadataChildDefault.shape input) next
      exact GeneralBorrowFreshMetadataChildProtector.staged tree _ parent node (GeneralBorrowFreshDefaultChild.child newTag parent)
        _ _ next parentPresent nodeFresh different
  | reuse index available valid vacant slack =>
    let input : GeneralBorrowFreshMetadataChildDefaultReuse.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,node,tagPresent,parentPresent,fresh,
        index,available,valid,vacant,slack,offset,len,nonzero,well,bounds⟩
    constructor
    · intro mapFresh
      change GeneralBorrowTagMap.Fresh (GeneralBorrowFreshMetadataChildDefaultReuse.result input).tagMapping next
      rw [(GeneralBorrowFreshMetadataChildDefaultReuse.reuse input).mapping]
      exact GeneralBorrowFreshMetadataChildAllocator.fresh_push tree.tagMapping newTag next _ _ mapFresh different
    · apply GeneralBorrowFreshMetadataChildProtector.of_shape _ _ (GeneralBorrowFreshMetadataChildDefaultReuse.shape input) next
      exact GeneralBorrowFreshMetadataChildProtector.staged tree _ parent node (GeneralBorrowFreshDefaultChild.child newTag parent)
        _ _ next parentPresent nodeFresh different

end DuplicatePrefix.GeneralRootDefaultFreshSlot
