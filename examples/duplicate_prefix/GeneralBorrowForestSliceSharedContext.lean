import duplicate_prefix.GeneralBorrowForestSliceSharedMetadata
import duplicate_prefix.GeneralBorrowFreshSharedSlotFlags
import duplicate_prefix.GeneralBorrowFreshMetadataChildOld

namespace DuplicatePrefix.GeneralBorrowForestSliceSharedContext
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestSharedData (registered)
open GeneralBorrowForestSliceShared
open GeneralBorrowFreshReadFrame
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- The newly constructed child becomes the next concrete source in the SAME
primary component and extra-root schedule. Actual graph/protector/range data
form all Context fields, including every old and new node's unexposed flag.
No successful-operation or poststate Context premise is supplied. -/
noncomputable def next (tree : BorrowTree) (protections : ProtectedTags) (newTag : BorTag) (isProtected : Bool)
    (parent primary : UniIndex) (extras : List UniIndex) (offset len : UInt64) (mode : ChildrenVisitMode)
    (data : Data tree protections newTag isProtected parent primary extras offset len mode)
    (covered : GeneralBorrowGraph.RootsCover tree) :
    GeneralBorrowForestAccessData.Context (child data).tree
      (GeneralBorrowFreshMetadataChildSlot.index data.slot) primary extras := by
  apply Classical.choice
  let metadata := GeneralBorrowForestSliceSharedMetadata.build tree protections newTag isProtected parent primary extras offset len mode data covered
  obtain ⟨newNode,newPresent,tagged,newFlag⟩ := metadata.node
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
  have tag : accessed.tree.indexOfTag data.parentTag = some parent := by
    change accessed.tree.tagMapping.get _ = _
    rw [mapping]
    exact data.tagPresent
  have fresh : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping newTag := by rw [mapping];exact data.fresh
  let slot := GeneralBorrowFreshMetadataChildSlot.transport tree accessed.tree data.context.depth depth nodes mapping rfl parent data.slot
  have bounds : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [good.2.2];exact data.bounds
  have primaryPresent : accessed.tree.nodeAt primary = some data.context.primaryNode := by
    change accessed.tree.nodes.get primary = _
    rw [nodes]
    exact data.context.primaryPresent
  obtain ⟨nextPrimary,primaryLookup,primaryTag,primaryFlag⟩ := GeneralBorrowFreshMetadataChildOld.of_slot
    accessed.tree depth children coverage data.parentTag newTag parent data.context.anchorNode
    tag present fresh slot isProtected offset len data.nonzero good.2.1 bounds primary data.context.primaryNode primaryPresent
  have initialFlags : GeneralBorrowFreshSharedSlotFlags.Unexposed accessed.tree := by
    intro query node lookup
    change accessed.tree.nodes.get query = _ at lookup
    rw [nodes] at lookup
    exact data.context.unexposed query node lookup
  have finalFlags := GeneralBorrowFreshSharedSlotFlags.of_slot accessed.tree depth children coverage
    data.parentTag newTag parent data.context.anchorNode tag present fresh slot isProtected offset len
    data.nonzero good.2.1 bounds initialFlags
  refine ⟨{
    anchorNode := newNode
    primaryNode := nextPrimary
    depth := metadata.certificates.depth
    children := metadata.certificates.children
    anchorPresent := newPresent
    primaryPresent := primaryLookup
    roots := metadata.roots.trans data.context.roots
    different := data.context.different
    unexposed := ?_ }⟩
  exact finalFlags

end DuplicatePrefix.GeneralBorrowForestSliceSharedContext
