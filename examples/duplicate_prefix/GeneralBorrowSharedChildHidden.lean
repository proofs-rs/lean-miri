import duplicate_prefix.GeneralBorrowSharedReadMetadata
namespace DuplicatePrefix.GeneralBorrowSharedChildHidden
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
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) sharedState) .Frozen held
    ∃ child node,actual.tree.indexOfTag newTag = some child ∧ actual.tree.nodeAt child = some node ∧
      node.tag = newTag ∧ node.isExposed = false := by
  let rank := GeneralBorrowStructuralHistoryShared.depth tree runtime.formed.toState
  have slot := GeneralBorrowStructuralHistoryShared.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree accounting fits =>
    let input : GeneralBorrowFreshMetadataChildShared.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,accounting,fits,held,offset,len,nonzero,runtime.formed.well,bounds⟩
    have output := GeneralBorrowFreshMetadataChildShared.append input
    obtain ⟨node,found,tag,ancestor,children,permission,hidden⟩ := output.newNode
    exact ⟨_,node,output.freshLookup,found,tag,hidden⟩
  | reuse child available valid vacant slack =>
    let input : GeneralBorrowFreshMetadataChildSharedReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        child,available,valid,vacant,slack,held,offset,len,nonzero,runtime.formed.well,bounds⟩
    have output := GeneralBorrowFreshMetadataChildSharedReuse.reuse input
    obtain ⟨node,found,tag,ancestor,children,permission,hidden⟩ := output.newNode
    exact ⟨_,node,output.freshLookup,found,tag,hidden⟩
end DuplicatePrefix.GeneralBorrowSharedChildHidden
