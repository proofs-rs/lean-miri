import duplicate_prefix.GeneralBorrowForestSliceShared
import duplicate_prefix.GeneralBorrowFreshMetadataChildSlot
import duplicate_prefix.GeneralBorrowFreshSharedGeometry

namespace DuplicatePrefix.GeneralBorrowForestSliceSharedMetadata
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestSharedData (registered)
open GeneralBorrowForestSliceShared GeneralBorrowFreshReadFrame
open GeneralBorrowFreshReborrowStages (Slot)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def index {tree : BorrowTree} {protections : ProtectedTags} {newTag : BorTag} {isProtected : Bool}
    {parent primary : UniIndex} {extras : List UniIndex} {offset len : UInt64} {mode : ChildrenVisitMode}
    (data : Data tree protections newTag isProtected parent primary extras offset len mode) : UniIndex :=
  GeneralBorrowFreshMetadataChildSlot.index data.slot

/-- Real result metadata needed by a later general-root stage. -/
structure Output (tree : BorrowTree) (protections : ProtectedTags) (newTag : BorTag) (isProtected : Bool)
    (parent primary : UniIndex) (extras : List UniIndex) (offset len : UInt64) (mode : ChildrenVisitMode)
    (data : Data tree protections newTag isProtected parent primary extras offset len mode) where
  certificates : GeneralBorrowFreshMetadataChildAttach.Certificates (child data).tree
  roots : (child data).tree.roots = tree.roots
  lookup : (child data).tree.indexOfTag newTag = some (index data)
  node : ∃ node, (child data).tree.nodeAt (index data) = some node ∧ node.tag = newTag ∧ node.isExposed = false
  well : (child data).tree.locations.WellFormed
  capacity : (child data).tree.locations.size = tree.locations.size

/-- Derive real append/reuse graph, tag, unexposed-child and partition metadata
from slice-local initial factory records and generic initial root coverage,
for either visitor mode. No outside-window ownership is required. -/
def build (tree : BorrowTree) (protections : ProtectedTags) (newTag : BorTag) (isProtected : Bool)
    (parent primary : UniIndex) (extras : List UniIndex) (offset len : UInt64) (mode : ChildrenVisitMode)
    (data : Data tree protections newTag isProtected parent primary extras offset len mode)
    (covered : GeneralBorrowGraph.RootsCover tree) :
    Output tree protections newTag isProtected parent primary extras offset len mode data := by
  have good := GeneralBorrowForestSliceAccess.access tree (registered protections newTag isProtected) data.parentTag
    parent primary extras (Size.ofBytes offset) (Size.ofBytes len) .Read mode data.context data.tagPresent data.well
    offset (offset+len) data.locations data.bounds (Nat.le_refl _) (Nat.le_refl _)
  change (read data).status = .Completed ∧ (read data).tree.locations.WellFormed ∧
    (read data).tree.locations.size = tree.locations.size at good
  let accessed := read data
  have frame := GeneralBorrowFreshReadFrame.frame tree (.concrete data.parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read (registered protections newTag isProtected) mode
  change accessed.tree = {tree with locations := accessed.tree.locations} at frame
  have nodes : accessed.tree.nodes = tree.nodes := by simpa only using congrArg BorrowTree.nodes frame
  have mapping : accessed.tree.tagMapping = tree.tagMapping := by simpa only using congrArg BorrowTree.tagMapping frame
  let depth := depth_on tree accessed.tree nodes data.context.depth
  have children : GeneralBorrowGraph.ChildNodes accessed.tree := by rw [frame];exact data.context.children
  have coverage : GeneralBorrowGraph.RootsCover accessed.tree := by rw [frame];exact covered
  have present : accessed.tree.nodeAt parent = some data.context.anchorNode := by
    change accessed.tree.nodes.get parent = _
    rw [nodes]
    exact data.context.anchorPresent
  have tag : accessed.tree.tagMapping.get data.parentTag = some parent := by rw [mapping];exact data.tagPresent
  have fresh : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping newTag := by rw [mapping];exact data.fresh
  have bounds : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [good.2.2];exact data.bounds
  let slot := GeneralBorrowFreshMetadataChildSlot.transport tree accessed.tree data.context.depth depth nodes mapping rfl parent data.slot
  have slotIndex := GeneralBorrowFreshMetadataChildSlot.transport_index tree accessed.tree data.context.depth depth nodes mapping rfl parent data.slot
  have slotEq : GeneralBorrowFreshMetadataChildSlot.index slot = GeneralBorrowFreshMetadataChildSlot.index data.slot := slotIndex
  have metadata := GeneralBorrowFreshMetadataChildSlot.build accessed.tree depth children coverage data.parentTag newTag parent data.context.anchorNode
    tag present fresh slot isProtected offset len data.nonzero good.2.1 bounds
  have geometry : (child data).tree.locations.WellFormed ∧ (child data).tree.locations.size = accessed.tree.locations.size := by
    cases slot with
    | append noFree aligned fits =>
      exact GeneralBorrowFreshSharedGeometry.append_frame
        ⟨accessed.tree,depth,children,coverage,data.parentTag,newTag,parent,data.context.anchorNode,tag,present,fresh,
          noFree,aligned,fits,isProtected,offset,len,data.nonzero,good.2.1,bounds⟩
    | reuse child available bounded vacant slack =>
      exact GeneralBorrowFreshSharedGeometry.reuse_frame
        ⟨accessed.tree,depth,children,coverage,data.parentTag,newTag,parent,data.context.anchorNode,tag,present,fresh,
          child,available,bounded,vacant,slack,isProtected,offset,len,data.nonzero,good.2.1,bounds⟩
  refine ⟨metadata.certificates,?_,?_,?_,geometry.1,geometry.2.trans good.2.2⟩
  · have rootsFrame : accessed.tree.roots = tree.roots := by simpa only using congrArg BorrowTree.roots frame
    exact metadata.roots.trans rootsFrame
  · simpa only [slotEq,index,GeneralBorrowFreshMetadataChildSlot.result,GeneralBorrowForestSliceShared.child,accessed] using metadata.lookup
  · simpa only [slotEq,index,GeneralBorrowFreshMetadataChildSlot.result,GeneralBorrowForestSliceShared.child,accessed] using metadata.node

end DuplicatePrefix.GeneralBorrowForestSliceSharedMetadata
