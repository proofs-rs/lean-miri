import duplicate_prefix.GeneralBorrowFreshSharedGeometry
import duplicate_prefix.GeneralBorrowFreshReborrowStages
namespace DuplicatePrefix.GeneralBorrowForestSharedSlotGeometry
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshReborrowStages GeneralBorrowFreshAnchor
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
/-- Shared construction retains partition geometry for any root forest and
either allocator branch; only initial graph and range metadata are used. -/
theorem geometry (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (children : GeneralBorrowGraph.ChildNodes tree) (covered : GeneralBorrowGraph.RootsCover tree)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagPresent : tree.indexOfTag parentTag = some parent) (parentPresent : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (slot : Slot tree depth parent)
    (isProtected : Bool) (offset len : UInt64) (nonzero : len ≠ 0)
    (well : tree.locations.WellFormed) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    let child := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) sharedState) .Frozen isProtected
    child.tree.locations.WellFormed ∧ child.tree.locations.size = tree.locations.size := by
  cases slot with
  | append noFree aligned fits =>
    exact GeneralBorrowFreshSharedGeometry.append_frame
      ⟨tree,depth,children,covered,parentTag,newTag,parent,parentNode,tagPresent,parentPresent,fresh,
        noFree,aligned,fits,isProtected,offset,len,nonzero,well,bounds⟩
  | reuse child available bounded vacant slack =>
    exact GeneralBorrowFreshSharedGeometry.reuse_frame
      ⟨tree,depth,children,covered,parentTag,newTag,parent,parentNode,tagPresent,parentPresent,fresh,
        child,available,bounded,vacant,slack,isProtected,offset,len,nonzero,well,bounds⟩
end DuplicatePrefix.GeneralBorrowForestSharedSlotGeometry
