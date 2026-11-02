import duplicate_prefix.GeneralBorrowForestSliceShared
import duplicate_prefix.GeneralBorrowForestSliceOwner
import duplicate_prefix.GeneralBorrowFreshSharedSlotOwned

namespace DuplicatePrefix.GeneralBorrowForestSliceSharedChild
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestSharedData (registered)
open GeneralBorrowFreshReadFrame
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- The actual registered-protector Read plus Frozen constructor forms the
NEW child's own slice-local Read contract. Arbitrary finite extra unexposed
subtrees, both normal visitor modes and either actual allocator branch are
supported. No outside-window ownership or operation-success input is required.
The registered protection map is used throughout, including protected children. -/
theorem run (tree : BorrowTree) (protections : ProtectedTags) (newTag : BorTag) (isProtected : Bool)
    (parent primary : UniIndex) (extras : List UniIndex) (offset len : UInt64) (mode : ChildrenVisitMode)
    (data : GeneralBorrowForestSliceShared.Data tree protections newTag isProtected parent primary extras offset len mode)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (locations : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowForestSliceOwner.InputLocation tree location (registered protections newTag isProtected)
        parent primary extras .Read .Read mode)) offset (offset+len) tree.locations) :
    (GeneralBorrowForestSliceShared.read data).status = .Completed ∧
    (GeneralBorrowForestSliceShared.child data).outcome = .ok () ∧
    GeneralRangeMapOrigins.OwnedOn
      (GeneralBorrowRange.LocationOwned (GeneralBorrowForestSliceShared.child data).tree (registered protections newTag isProtected)
        (GeneralBorrowFreshMetadataChildSlot.index data.slot) .Read)
      offset (offset+len) (GeneralBorrowForestSliceShared.child data).tree.locations := by
  have accessedGood := GeneralBorrowForestSliceOwner.access tree (registered protections newTag isProtected) data.parentTag parent primary extras
    (Size.ofBytes offset) (Size.ofBytes len) .Read .Read mode data.context data.tagPresent data.well fits (fun same => same)
    offset (offset+len) locations data.bounds (Nat.le_refl _) (Nat.le_refl _)
  change (GeneralBorrowForestSliceShared.read data).status = .Completed ∧
    GeneralRangeMapOrigins.OwnedOn
      (GeneralBorrowRange.LocationOwned (GeneralBorrowForestSliceShared.read data).tree (registered protections newTag isProtected) parent .Read)
      offset (offset+len) (GeneralBorrowForestSliceShared.read data).tree.locations ∧
    (GeneralBorrowForestSliceShared.read data).tree.locations.WellFormed ∧
    (GeneralBorrowForestSliceShared.read data).tree.locations.size = tree.locations.size at accessedGood
  let accessed := GeneralBorrowForestSliceShared.read data
  have frame := GeneralBorrowFreshReadFrame.frame tree (.concrete data.parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read (registered protections newTag isProtected) mode
  change accessed.tree = {tree with locations := accessed.tree.locations} at frame
  have nodes : accessed.tree.nodes = tree.nodes := by simpa only using congrArg BorrowTree.nodes frame
  have mapping : accessed.tree.tagMapping = tree.tagMapping := by simpa only using congrArg BorrowTree.tagMapping frame
  let depth := depth_on tree accessed.tree nodes data.context.depth
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
  have indexEq := GeneralBorrowFreshMetadataChildSlot.transport_index tree accessed.tree data.context.depth depth nodes mapping rfl parent data.slot
  have bounds : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [accessedGood.2.2.2];exact data.bounds
  have newFits : accessed.tree.nodes.data.size ≤ 4294967296 := by rw [nodes];exact fits
  have childOwned := GeneralBorrowFreshSharedSlotOwned.owned accessed.tree depth data.parentTag newTag parent data.context.anchorNode
    tag present fresh slot newFits isProtected offset len data.nonzero accessedGood.2.2.1 bounds
    (registered protections newTag isProtected) accessedGood.2.1
  refine ⟨accessedGood.1,childOwned.1,?_⟩
  have slotEq : GeneralBorrowFreshMetadataChildSlot.index slot = GeneralBorrowFreshMetadataChildSlot.index data.slot := indexEq
  simpa only [slotEq,GeneralBorrowForestSliceShared.child,accessed] using childOwned.2

end DuplicatePrefix.GeneralBorrowForestSliceSharedChild
