import duplicate_prefix.GeneralBorrowForestArgumentCopy
import duplicate_prefix.GenericFunctionEntryFreshness

namespace DuplicatePrefix.GeneralBorrowForestEntryFreshness
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshReadFrame GeneralBorrowFreshReborrowStages
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- INITIAL future node-tag freshness survives the real multiple-root FnEntry
Read and protected reservation. This is not global-unheld freshness. -/
theorem future (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (data : GeneralBorrowForestEntryValidity.Data tree tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (future : BorTag) (nodeFresh : GeneralBorrowProtector.Fresh tree future)
    (different : tracker.global.nextPointerTag ≠ future) :
    GeneralBorrowProtector.Fresh (GeneralBorrowForestArgumentCopy.finalTree tree tracker parentTag offset len) future := by
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
  have nodes : accessed.tree.nodes = tree.nodes := by simpa only using congrArg BorrowTree.nodes framed
  have mapping : accessed.tree.tagMapping = tree.tagMapping := by simpa only using congrArg BorrowTree.tagMapping framed
  let depth := depth_on tree accessed.tree nodes data.context.depth
  have parentPresent : accessed.tree.nodeAt data.parent = some data.context.anchorNode := by change accessed.tree.nodes.get data.parent = _;rw [nodes];exact data.context.anchorPresent
  have tagPresent : accessed.tree.tagMapping.get parentTag = some data.parent := by rw [mapping];exact data.tagPresent
  have fresh : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping tracker.global.nextPointerTag := by rw [mapping];exact data.tagFresh
  have nextBounds : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [good.2.2.2];exact bounds
  have fits : accessed.tree.nodes.data.size ≤ 4294967296 := by rw [nodes];exact data.nodeFits
  have nextNodeFresh : GeneralBorrowProtector.Fresh accessed.tree future := by
    unfold GeneralBorrowProtector.Fresh at nodeFresh ⊢
    rw [nodes]
    exact nodeFresh
  let slot := GeneralBorrowFreshMetadataChildMutableSlot.transport tree accessed.tree data.context.depth depth nodes mapping rfl data.parent data.slot
  have result := GenericFunctionEntryFreshness.mutable_slot accessed.tree depth
    (by rw [framed];exact data.context.children) (by rw [framed];exact data.covered)
    parentTag tracker.global.nextPointerTag data.parent data.context.anchorNode tagPresent parentPresent fresh slot
    offset len nonzero good.2.2.1 nextBounds future nextNodeFresh different
  simpa only [GeneralBorrowForestArgumentCopy.finalTree,accessed,registered,TypedBorrowSteps.registeredGlobal,
    GeneralBorrowFreshMetadataChildMutableSlot.result] using result.2

end DuplicatePrefix.GeneralBorrowForestEntryFreshness
