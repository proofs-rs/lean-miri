import duplicate_prefix.GeneralBorrowForestArgumentCopy
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutableSlot

namespace DuplicatePrefix.GeneralBorrowForestEntryMetadata
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshReadFrame GeneralBorrowFreshReborrowStages
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

set_option autoImplicit false in
structure Output (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag)
    (offset len : UInt64)
    (data : GeneralBorrowForestEntryValidity.Data tree tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len) where
  certificates : GeneralBorrowFreshMetadataChildAttach.Certificates
    (GeneralBorrowForestArgumentCopy.finalTree tree tracker parentTag offset len)
  roots : (GeneralBorrowForestArgumentCopy.finalTree tree tracker parentTag offset len).roots = tree.roots
  lookup : (GeneralBorrowForestArgumentCopy.finalTree tree tracker parentTag offset len).indexOfTag tracker.global.nextPointerTag =
    some (GeneralBorrowFreshMetadataChildMutableSlot.index data.slot)
  node : ∃ node, (GeneralBorrowForestArgumentCopy.finalTree tree tracker parentTag offset len).nodeAt
    (GeneralBorrowFreshMetadataChildMutableSlot.index data.slot) = some node ∧ node.tag = tracker.global.nextPointerTag ∧ node.isExposed = false
  nodeFits : (GeneralBorrowForestArgumentCopy.finalTree tree tracker parentTag offset len).nodes.data.size ≤ 4294967296
  well : (GeneralBorrowForestArgumentCopy.finalTree tree tracker parentTag offset len).locations.WellFormed
  capacity : (GeneralBorrowForestArgumentCopy.finalTree tree tracker parentTag offset len).locations.size = tree.locations.size

set_option autoImplicit false in
/-- Graph and allocator metadata of the actual ROOT mutable child, derived from
initial caller-tree data through protector insertion, Read, and construction. -/
def build (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (data : GeneralBorrowForestEntryValidity.Data tree tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) : Output tree tracker parentTag offset len data := by
  let registered := tracker.global.protectedTags.insert tracker.global.nextPointerTag .StrongProtector
  let accessed := tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registered .VisitChildrenOfAccessed
  have owners := GeneralBorrowForestMutableRegister.registered tree tracker.global {} ⟨1,by decide⟩ tracker.global.nextPointerTag .StrongProtector
    data.parent data.primary data.extras data.tagFresh data.nodeTags data.globalUnheld offset (offset+len) data.owned
  have good := GeneralBorrowForestMutableSlice.access tree registered parentTag data.parent data.primary data.extras
    (Size.ofBytes offset) (Size.ofBytes len) .Read .VisitChildrenOfAccessed data.context data.tagPresent data.well data.nodeFits
    offset (offset+len) owners.2.2.2 bounds (Nat.le_refl _) (Nat.le_refl _)
  change accessed.status = .Completed ∧ GeneralRangeMapOrigins.OwnedOn
    (fun location => Nonempty (GeneralBorrowForestMutableAccess.Data accessed.tree location registered data.parent data.primary data.extras))
    offset (offset+len) accessed.tree.locations ∧ accessed.tree.locations.WellFormed ∧ accessed.tree.locations.size = tree.locations.size at good
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
  let depth := depth_on tree accessed.tree nodes data.context.depth
  have children : GeneralBorrowGraph.ChildNodes accessed.tree := by rw [framed];exact data.context.children
  have covered : GeneralBorrowGraph.RootsCover accessed.tree := by rw [framed];exact data.covered
  have parentPresent : accessed.tree.nodeAt data.parent = some data.context.anchorNode := by
    change accessed.tree.nodes.get data.parent = _;rw [nodes];exact data.context.anchorPresent
  have tagPresent : accessed.tree.tagMapping.get parentTag = some data.parent := by rw [mapping];exact data.tagPresent
  have fresh : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping tracker.global.nextPointerTag := by rw [mapping];exact data.tagFresh
  have fits : accessed.tree.nodes.data.size ≤ 4294967296 := by rw [nodes];exact data.nodeFits
  have bounded : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [good.2.2.2];exact bounds
  let slot := GeneralBorrowFreshMetadataChildMutableSlot.transport tree accessed.tree data.context.depth depth nodes mapping rfl data.parent data.slot
  have indexEq : GeneralBorrowFreshMetadataChildMutableSlot.index slot = GeneralBorrowFreshMetadataChildMutableSlot.index data.slot := by
    dsimp only [slot]
    rw [GeneralBorrowFreshMetadataChildMutableSlot.transport_index]
  have metadata := GeneralBorrowFreshMetadataChildMutableSlot.build accessed.tree depth children covered parentTag tracker.global.nextPointerTag
    data.parent data.context.anchorNode tagPresent parentPresent fresh slot offset len nonzero good.2.2.1 fits bounded
  have sameTree : GeneralBorrowFreshMetadataChildMutableSlot.result accessed.tree parentTag tracker.global.nextPointerTag offset len =
      GeneralBorrowForestArgumentCopy.finalTree tree tracker parentTag offset len := rfl
  refine ⟨metadata.certificates,metadata.roots.trans roots,?_,?_,metadata.nodeFits,metadata.well,metadata.capacity.trans good.2.2.2⟩
  · simpa only [indexEq,sameTree] using metadata.lookup
  · simpa only [indexEq,sameTree] using metadata.node

end DuplicatePrefix.GeneralBorrowForestEntryMetadata
