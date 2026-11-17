import duplicate_prefix.GenericFunctionEntryOwnership
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutableSlot

namespace DuplicatePrefix.GenericFunctionEntryMetadata
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshReadFrame GeneralBorrowFreshReborrowStages
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

set_option autoImplicit false in
structure Output (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag)
    (offset len : UInt64)
    (data : GenericAsMutPtrEntryValidity.Data tree tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len) where
  certificates : GeneralBorrowFreshMetadataChildAttach.Certificates
    (GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len)
  roots : (GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len).roots = #[data.root]
  lookup : (GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len).indexOfTag tracker.global.nextPointerTag =
    some (GeneralBorrowFreshMutableStages.slot_index data.slot)
  node : ∃ node, (GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len).nodeAt
    (GeneralBorrowFreshMutableStages.slot_index data.slot) = some node ∧ node.tag = tracker.global.nextPointerTag ∧ node.isExposed = false
  nodeFits : (GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len).nodes.data.size ≤ 4294967296
  well : (GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len).locations.WellFormed
  capacity : (GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len).locations.size = tree.locations.size

set_option autoImplicit false in
/-- Graph and allocator metadata of the actual ROOT mutable child, derived from
initial caller-tree data through protector insertion, Read, and construction. -/
def build (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (data : GenericAsMutPtrEntryValidity.Data tree tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) : Output tree tracker parentTag offset len data := by
  let registered := tracker.global.protectedTags.insert tracker.global.nextPointerTag .StrongProtector
  let accessed := tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registered .VisitChildrenOfAccessed
  have owners := protector_owned_on tree tracker.global.protectedTags tracker.global.nextPointerTag .StrongProtector
    data.protectorFresh data.parent .Write offset (offset+len) data.owned
  have good := GeneralBorrowRangeLocal.access tree registered parentTag data.parent data.root (Size.ofBytes offset) (Size.ofBytes len)
    .Read .Write .VisitChildrenOfAccessed (fun _ => rfl) data.nodeFits data.depth data.children data.node data.parentPresent
    data.roots data.covered data.tagPresent data.well offset (offset+len) owners bounds (Nat.le_refl _) (Nat.le_refl _)
  change accessed.status = .Completed ∧ GeneralRangeMapOrigins.OwnedOn
    (GeneralBorrowRange.LocationOwned accessed.tree registered data.parent .Write) offset (offset+len) accessed.tree.locations ∧
    accessed.tree.locations.WellFormed ∧ accessed.tree.locations.size = tree.locations.size at good
  have framed := GeneralBorrowFreshReadFrame.frame tree (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registered .VisitChildrenOfAccessed
  change accessed.tree = {tree with locations := accessed.tree.locations} at framed
  have nodes : accessed.tree.nodes = tree.nodes := by
    have equality := congrArg BorrowTree.nodes framed
    exact equality
  have mapping : accessed.tree.tagMapping = tree.tagMapping := by
    have equality := congrArg BorrowTree.tagMapping framed
    exact equality
  have roots : accessed.tree.roots = tree.roots := by
    have equality := congrArg BorrowTree.roots framed
    exact equality
  let depth := depth_on tree accessed.tree nodes data.depth
  have children : GeneralBorrowGraph.ChildNodes accessed.tree := by rw [framed];exact data.children
  have covered : GeneralBorrowGraph.RootsCover accessed.tree := by rw [framed];exact data.covered
  have parentPresent : accessed.tree.nodeAt data.parent = some data.node := by
    change accessed.tree.nodes.get data.parent = _;rw [nodes];exact data.parentPresent
  have tagPresent : accessed.tree.tagMapping.get parentTag = some data.parent := by rw [mapping];exact data.tagPresent
  have fresh : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping tracker.global.nextPointerTag := by rw [mapping];exact data.tagFresh
  have fits : accessed.tree.nodes.data.size ≤ 4294967296 := by rw [nodes];exact data.nodeFits
  have bounded : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [good.2.2.2];exact bounds
  let slot := GeneralBorrowFreshMetadataChildMutableSlot.transport tree accessed.tree data.depth depth nodes mapping rfl data.parent data.slot
  have indexEq : GeneralBorrowFreshMetadataChildMutableSlot.index slot = GeneralBorrowFreshMutableStages.slot_index data.slot := by
    dsimp only [slot]
    rw [GeneralBorrowFreshMetadataChildMutableSlot.transport_index]
    cases data.slot <;> rfl
  have metadata := GeneralBorrowFreshMetadataChildMutableSlot.build accessed.tree depth children covered parentTag tracker.global.nextPointerTag
    data.parent data.node tagPresent parentPresent fresh slot offset len nonzero good.2.2.1 fits bounded
  have sameTree : GeneralBorrowFreshMetadataChildMutableSlot.result accessed.tree parentTag tracker.global.nextPointerTag offset len =
      GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len := rfl
  refine ⟨metadata.certificates,metadata.roots.trans (roots.trans data.roots),?_,?_,metadata.nodeFits,metadata.well,metadata.capacity.trans good.2.2.2⟩
  · simpa only [indexEq,sameTree] using metadata.lookup
  · simpa only [indexEq,sameTree] using metadata.node

end DuplicatePrefix.GenericFunctionEntryMetadata
