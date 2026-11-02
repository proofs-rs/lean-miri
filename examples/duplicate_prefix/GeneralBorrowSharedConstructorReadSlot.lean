import duplicate_prefix.GeneralBorrowSharedConstructorReadPreserves
import duplicate_prefix.GeneralBorrowFreshReborrowStages

namespace DuplicatePrefix.GeneralBorrowSharedConstructorReadSlot
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowGraph DuplicatePrefix.GeneralRangeMapOrigins
open DuplicatePrefix.GeneralBorrowFreshReborrowStages
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- The actual unprotected shared constructor preserves any pre-existing Read
anchor on its selected range, for both real allocator branches. Initial present
node and allocator data derive that a reused slot cannot be the old anchor. -/
theorem owned (tree : BorrowTree) (depth : ParentDepth tree.nodes) (children : ChildNodes tree) (covered : RootsCover tree)
    (parentTag tag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (parentTagPresent : tree.indexOfTag parentTag = some parent) (parentPresent : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (slot : Slot tree depth parent)
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) (fits : tree.nodes.data.size ≤ 4294967296)
    (target : UniIndex) (targetPresent : ∃ node, tree.nodeAt target = some node)
    (before : OwnedOn (GeneralBorrowRange.LocationOwned tree {} target .Read) offset (offset+len) tree.locations) :
    let result := tree.newChild (Size.ofBytes offset) (.concrete parentTag) tag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen false
    OwnedOn (GeneralBorrowRange.LocationOwned result.tree {} target .Read) offset (offset+len) result.tree.locations := by
  dsimp only
  cases slot with
  | append noFree aligned indexFits =>
    let input : GeneralBorrowFreshMetadataChildShared.Input :=
      ⟨tree,depth,children,covered,parentTag,tag,parent,parentNode,parentTagPresent,parentPresent,fresh,
        noFree,aligned,indexFits,false,offset,len,nonzero,well,bounds⟩
    exact GeneralBorrowSharedConstructorReadPreserves.Append.owned input target before
  | reuse index available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildSharedReuse.Input :=
      ⟨tree,depth,children,covered,parentTag,tag,parent,parentNode,parentTagPresent,parentPresent,fresh,
        index,available,bounded,vacant,slack,false,offset,len,nonzero,well,bounds⟩
    have different : target ≠ index := by
      intro same
      obtain ⟨node,present⟩ := targetPresent
      rw [same] at present
      change tree.nodes.get index = some node at present
      rw [vacant] at present
      cases present
    exact GeneralBorrowSharedConstructorReadPreserves.Reuse.owned input target different fits before

end DuplicatePrefix.GeneralBorrowSharedConstructorReadSlot
