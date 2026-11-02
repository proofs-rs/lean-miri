import duplicate_prefix.GeneralBorrowSharedReadMetadata
import duplicate_prefix.GeneralBorrowFreshParentTagOrder
namespace DuplicatePrefix.GeneralBorrowSharedChildParentTagOrder
open Miri Miri.Memory Miri.ABI Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshAnchor
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- Actual append/reuse metadata fixes the hidden fresh shared child. -/
theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (held : Bool) (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (parentOrder : parentNode.tag.value ≤ newTag.value) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) sharedState) .Frozen held
    GeneralBorrowWildcardParentTagOrder.ParentTagOrder actual.tree := by
  let rank := GeneralBorrowStructuralHistoryShared.depth tree runtime.formed.toState
  have slot := GeneralBorrowStructuralHistoryShared.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree accounting fits =>
    let input : GeneralBorrowFreshMetadataChildShared.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,accounting,fits,held,offset,len,nonzero,runtime.formed.well,bounds⟩
    exact GeneralBorrowFreshParentTagOrder.staged_order tree rank order _ parent parentNode
      (sharedNode newTag parent)
      (GeneralBorrowFreshParentTagOrder.vacant_at_end tree _ (GeneralBorrowFreshMetadataChildShared.at_end input))
      present rfl parentOrder _ _ _ (GeneralBorrowFreshMetadataChildShared.shape input)
  | reuse child available valid vacant slack =>
    let input : GeneralBorrowFreshMetadataChildSharedReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        child,available,valid,vacant,slack,held,offset,len,nonzero,runtime.formed.well,bounds⟩
    exact GeneralBorrowFreshParentTagOrder.staged_order tree rank order child parent parentNode
      (sharedNode newTag parent) vacant present rfl parentOrder _ _ _ (GeneralBorrowFreshMetadataChildSharedReuse.shape input)
end DuplicatePrefix.GeneralBorrowSharedChildParentTagOrder
