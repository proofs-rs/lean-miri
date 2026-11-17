import duplicate_prefix.GeneralBorrowFreshParentTagOrder
import duplicate_prefix.GeneralBorrowDefaultChildMetadata
namespace DuplicatePrefix.GeneralBorrowDefaultChildOrder
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowFreshMetadataChildDefaultSlot GeneralBorrowWildcardParentTagOrder
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- The actual unprotected Default constructor preserves conditional graph order;
append and coherent reuse share the same vacancy law. -/
theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (order : ParentTagOrder tree)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (freshOrder : parentNode.tag.value ≤ newTag.value)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    ParentTagOrder (result tree parentTag newTag offset len) := by
  let rank := GeneralBorrowStructuralHistoryDefault.depth tree runtime.formed.toState
  let slot := GeneralBorrowStructuralHistoryDefault.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildDefault.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,aligned,fits,offset,len,nonzero,runtime.formed.well,bounds⟩
    exact GeneralBorrowFreshParentTagOrder.staged_order tree rank order _ parent parentNode _
      (GeneralBorrowFreshParentTagOrder.vacant_at_end tree _ (GeneralBorrowFreshMetadataChildDefault.at_end input))
      present rfl freshOrder _ _ _ (GeneralBorrowFreshMetadataChildDefault.shape input)
  | reuse child available valid vacant slack =>
    let input : GeneralBorrowFreshMetadataChildDefaultReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        child,available,valid,vacant,slack,offset,len,nonzero,runtime.formed.well,bounds⟩
    exact GeneralBorrowFreshParentTagOrder.staged_order tree rank order child parent parentNode _ vacant
      present rfl freshOrder _ _ _ (GeneralBorrowFreshMetadataChildDefaultReuse.shape input)
end DuplicatePrefix.GeneralBorrowDefaultChildOrder
