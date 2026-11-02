import duplicate_prefix.GeneralBorrowCanonicalParentDepth
import duplicate_prefix.GeneralBorrowForestDefaultStageVacantClean
import duplicate_prefix.GeneralBorrowForestAsMutDefaultResources
import duplicate_prefix.GeneralBorrowForestEntryValidity
import duplicate_prefix.GeneralBorrowForestForeignSharedFresh
import duplicate_prefix.GeneralBorrowFreshSharedWithinStages
namespace DuplicatePrefix.GeneralBorrowForestDefaultStageNext
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshReadFrame GeneralBorrowFreshReborrowStages
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.dsimp.instances true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency false
noncomputable section
structure Output (tree : BorrowTree) (protections : ProtectedTags) (parentTag newTag : BorTag) (offset len : UInt64) where
  data : GeneralBorrowForestEntryValidity.Data tree protections parentTag newTag offset len
  clean : GeneralRangeMapState.Every
    (fun location : LocationTree => location.perms.get (GeneralBorrowFreshMetadataChildMutableSlot.index data.slot) = none) tree.locations
  allocator : GeneralBorrowGcAllocator.Invariant tree
  vacantClean : GeneralBorrowGcVacantClean.VacantClean tree

def build (tree : BorrowTree) (protections : ProtectedTags) (newTag nextTag : BorTag) (parent : UniIndex) (offset len : UInt64)
    (data : GeneralBorrowForestAsMutDefaultSequence.Data tree newTag parent offset len)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowForestMutableAccess.Data tree location protections parent data.primary data.extras))
      offset (offset+len) tree.locations)
    (allocator : GeneralBorrowGcAllocator.Invariant tree) (clean : GeneralBorrowGcVacantClean.VacantClean tree)
    (futureFresh : GeneralBorrowTagMap.Fresh tree.tagMapping nextTag) (different : newTag ≠ nextTag)
    (unheld : protections.get nextTag = none) (room : tree.nodes.size+5 ≤ 4294967295) :
    Output (GeneralBorrowForestAsMutDefaultSequence.child data protections).tree protections newTag nextTag offset len := by
  let parentTag := data.parentTag
  have nonzero := data.nonzero
  have bounds := data.bounds
  let accessed := tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read protections .VisitChildrenOfAccessed
  have good := GeneralBorrowForestMutableSlice.access tree protections parentTag parent data.primary data.extras
    (Size.ofBytes offset) (Size.ofBytes len) .Read .VisitChildrenOfAccessed data.context data.parentTagPresent data.well data.nodeFits
    offset (offset+len) owned bounds (Nat.le_refl _) (Nat.le_refl _)
  change accessed.status = .Completed ∧ GeneralRangeMapOrigins.OwnedOn
    (fun location => Nonempty (GeneralBorrowForestMutableAccess.Data accessed.tree location protections parent data.primary data.extras))
    offset (offset+len) accessed.tree.locations ∧ accessed.tree.locations.WellFormed ∧ accessed.tree.locations.size = tree.locations.size at good
  have framed := GeneralBorrowFreshReadFrame.frame tree (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read protections .VisitChildrenOfAccessed
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
  have parentPresent : accessed.tree.nodeAt parent = some data.context.anchorNode := by
    change accessed.tree.nodes.get parent = _;rw [nodes];exact data.context.anchorPresent
  have tagPresent : accessed.tree.tagMapping.get parentTag = some parent := by rw [mapping];exact data.parentTagPresent
  have fresh : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping newTag := by rw [mapping];exact data.tagFresh
  have fits : accessed.tree.nodes.data.size ≤ 4294967296 := by rw [nodes];exact data.nodeFits
  have bounded : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [good.2.2.2];exact bounds
  let slot := GeneralBorrowFreshMetadataChildDefaultSlot.transport tree accessed.tree data.context.depth depth nodes mapping rfl parent data.slot
  have indexEq : GeneralBorrowFreshMetadataChildDefaultSlot.index slot = GeneralBorrowFreshMetadataChildDefaultSlot.index data.slot := by
    exact GeneralBorrowFreshMetadataChildDefaultSlot.transport_index tree accessed.tree data.context.depth depth nodes mapping rfl parent data.slot
  have metadata := GeneralBorrowFreshMetadataChildDefaultSlot.build accessed.tree depth children covered parentTag newTag
    parent data.context.anchorNode tagPresent parentPresent fresh slot offset len nonzero good.2.2.1 fits bounded
  have readAllocator : GeneralBorrowGcAllocator.Invariant accessed.tree := by
    rw [framed]
    exact ⟨allocator.pool,allocator.accounting,allocator.unique,allocator.nodeTags⟩
  have resources := GeneralBorrowForestAsMutDefaultResources.preserves accessed.tree depth children covered parentTag newTag parent data.context.anchorNode
    tagPresent parentPresent fresh slot offset len nonzero good.2.2.1 bounded readAllocator
  let after := (GeneralBorrowForestAsMutDefaultSequence.child data protections).tree
  have nextAllocator : GeneralBorrowGcAllocator.Invariant after := resources.1
  have nextClean := GeneralBorrowForestDefaultStageVacantClean.preserves tree protections newTag parent offset len data owned clean
  have ran := GeneralBorrowForestDefault.run tree protections parentTag newTag parent data.primary data.extras offset len .VisitChildrenOfAccessed
    data.context data.covered data.parentTagPresent data.tagFresh data.slot data.nodeFits nonzero data.well bounds owned
  let anchor := GeneralBorrowFreshMetadataChildDefaultSlot.index data.slot
  let nextContext := Classical.choice ran.2.2.1
  let nextDepth := GeneralBorrowCanonicalParentDepth.normalize after.nodes nextContext.depth
  let normalized : GeneralBorrowForestAccessData.Context after anchor data.primary data.extras := {nextContext with depth := nextDepth}
  have nextRoom : after.nodes.size+4 ≤ 4294967295 := by
    have size := resources.2.2.2
    rw [nodes] at size
    change after.nodes.size ≤ tree.nodes.size+1 at size
    omega
  have aligned := GeneralBorrowFreshStagePool.empty_aligned after nextAllocator.accounting
  have mappingFits : after.tagMapping.deassigned.back? = none → after.tagMapping.mapping.size ≤ 4294967295 := by
    intro empty
    rw [aligned empty]
    change after.nodes.data.size+4 ≤ _ at nextRoom
    omega
  let nextSlot := GeneralBorrowCanonicalParentDepth.slot after nextContext.depth anchor nextContext.anchorNode nextContext.anchorPresent
    nextAllocator.pool aligned mappingFits
  have nextFresh : GeneralBorrowTagMap.Fresh after.tagMapping nextTag := by
    apply GeneralBorrowForestForeignSharedFresh.fresh_of_absent
    have old := metadata.oldLookup nextTag different
    change after.indexOfTag nextTag = _ at old
    change after.indexOfTag nextTag = none
    rw [old]
    change accessed.tree.tagMapping.get nextTag = none
    rw [mapping]
    unfold UniKeyMap.get
    rw [GeneralBorrowTagMap.fresh_find tree.tagMapping nextTag futureFresh]
    rfl
  let nextData : GeneralBorrowForestEntryValidity.Data after protections newTag nextTag offset len := {
    parent := anchor,primary := data.primary,extras := data.extras,context := normalized,
    covered := ran.2.2.2.2.2.2.2.2,tagPresent := ran.2.2.2.2.1,tagFresh := nextFresh,globalUnheld := unheld,
    nodeTags := nextAllocator.nodeTags,nodeFits := ran.2.2.2.2.2.2.2.1,slot := nextSlot,
    well := resources.2.1,owned := ran.2.2.2.1 }
  refine ⟨nextData,?_,nextAllocator,nextClean⟩
  apply nextClean
  have vacant := GeneralBorrowFreshSharedWithinStages.slot_vacant after nextDepth anchor nextSlot
  cases nextSlot <;> exact vacant
end
end DuplicatePrefix.GeneralBorrowForestDefaultStageNext
