import duplicate_prefix.GeneralBorrowForestMixedSharedArgumentCopy
import duplicate_prefix.GeneralBorrowForestSharedWithinStages
import duplicate_prefix.GeneralBorrowForestSharedSlotGeometry
namespace DuplicatePrefix.GeneralBorrowForestMixedSharedReleaseData
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open GeneralBorrowForestMixedSharedArgumentCopy
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
theorem prepare
    (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState) (id : AllocId)
    (parentTag : BorTag) (parent primary : UniIndex) (extras : List UniIndex) (offset len : UInt64)
    (context : GeneralBorrowForestAccessData.Context tree parent primary extras)
    (covered : GeneralBorrowGraph.RootsCover tree)
    (tagPresent : tree.indexOfTag parentTag = some parent)
    (tagFresh : GeneralBorrowTagMap.Fresh tree.tagMapping tracker.global.nextPointerTag)
    (nodeTags : ∀ index node, tree.nodeAt index = some node → tree.indexOfTag node.tag = some index)
    (unheld : tracker.global.protectedTags.get tracker.global.nextPointerTag = none)
    (slot : GeneralBorrowFreshReborrowStages.Slot tree context.depth parent)
    (fits : tree.nodes.data.size ≤ 4294967296) (writable : Nat → Bool) (nonzero : len ≠ 0)
    (well : tree.locations.WellFormed) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree =>
      location.perms.get (GeneralBorrowFreshMetadataChildSlot.index slot) = none) tree.locations)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowForestMixedAccess.Data tree location tracker.global.protectedTags parent primary extras writable))
      offset (offset+len) tree.locations) :
    Nonempty (GeneralBorrowForestAccessData.Context (finalTree tree tracker parentTag offset len)
      (GeneralBorrowFreshMetadataChildSlot.index slot) primary extras) ∧
    GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowForestMixedAccess.Data (finalTree tree tracker parentTag offset len) location
        (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags
        (GeneralBorrowFreshMetadataChildSlot.index slot) primary extras
        (GeneralBorrowFreshMixedChild.extend writable (GeneralBorrowFreshMetadataChildSlot.index slot).toNat)))
      offset (offset+len) (finalTree tree tracker parentTag offset len).locations ∧
    (finalTree tree tracker parentTag offset len).indexOfTag tracker.global.nextPointerTag = some (GeneralBorrowFreshMetadataChildSlot.index slot) ∧
    (finalTree tree tracker parentTag offset len).locations.WellFormed ∧
    GeneralBorrowFreshReleaseLoop.ActiveOn (finalTree tree tracker parentTag offset len)
      (GeneralBorrowFreshMetadataChildSlot.index slot) .Read offset (offset+len) := by
  have own := GeneralBorrowForestMixedSharedArgumentCopy.final_owned tree tracker borrowFrame id parentTag parent primary extras
    offset len context covered tagPresent tagFresh nodeTags unheld slot fits writable nonzero well bounds owned
  have protectorFresh : GeneralBorrowProtector.Fresh tree tracker.global.nextPointerTag := by
    intro row member
    have present := (GeneralBorrowFreshReuseProtection.entries_get tree.nodes row.1 row.2).mp (Array.mem_toList_iff.mpr member)
    exact GeneralBorrowForestMixedRegister.node_fresh tree tracker.global.nextPointerTag tagFresh nodeTags row.1 row.2 present
  have activity := GeneralBorrowForestSharedWithinStages.borrow tree tracker.global.protectedTags true
    parentTag tracker.global.nextPointerTag parent primary extras context covered tagPresent tagFresh protectorFresh fits slot
    offset len nonzero well bounds writable owned clean
  let protections := (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags
  have registration := GeneralBorrowForestMixedRegister.registered tree tracker.global borrowFrame id
    tracker.global.nextPointerTag .StrongProtector parent primary extras writable tagFresh nodeTags unheld offset (offset+len) owned
  have good := GeneralBorrowForestMixedSlice.access tree protections parentTag parent primary extras (Size.ofBytes offset) (Size.ofBytes len)
    writable .VisitChildrenOfAccessed context tagPresent well fits offset (offset+len) registration.2.2.2 bounds (Nat.le_refl _) (Nat.le_refl _)
  let read := tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len) .Read protections .VisitChildrenOfAccessed
  have frame := GeneralBorrowFreshReadFrame.frame tree (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len) .Read protections .VisitChildrenOfAccessed
  change read.tree = {tree with locations := read.tree.locations} at frame
  have nodes : read.tree.nodes = tree.nodes := by simpa only using congrArg BorrowTree.nodes frame
  have mapping : read.tree.tagMapping = tree.tagMapping := by simpa only using congrArg BorrowTree.tagMapping frame
  let depth := GeneralBorrowFreshReadFrame.depth_on tree read.tree nodes context.depth
  let nextSlot := GeneralBorrowFreshMetadataChildSlot.transport tree read.tree context.depth depth nodes mapping rfl parent slot
  have slotEq := GeneralBorrowFreshMetadataChildSlot.transport_index tree read.tree context.depth depth nodes mapping rfl parent slot
  have present : read.tree.nodeAt parent = some context.anchorNode := by
    change read.tree.nodes.get parent = _
    rw [nodes]
    exact context.anchorPresent
  have nextTag : read.tree.indexOfTag parentTag = some parent := by rw [frame];exact tagPresent
  have nextFresh : GeneralBorrowTagMap.Fresh read.tree.tagMapping tracker.global.nextPointerTag := by rw [mapping];exact tagFresh
  have nextChildren : GeneralBorrowGraph.ChildNodes read.tree := by rw [frame];exact context.children
  have nextCovered : GeneralBorrowGraph.RootsCover read.tree := by rw [frame];exact covered
  have nextBounds : offset.toNat+len.toNat ≤ read.tree.locations.size.bytes.toNat := by rw [good.2.2.2];exact bounds
  have geometry := GeneralBorrowForestSharedSlotGeometry.geometry read.tree depth nextChildren nextCovered
    parentTag tracker.global.nextPointerTag parent context.anchorNode nextTag present nextFresh nextSlot true offset len nonzero good.2.2.1 nextBounds
  have metadata := GeneralBorrowFreshMetadataChildSlot.build read.tree depth nextChildren nextCovered
    parentTag tracker.global.nextPointerTag parent context.anchorNode nextTag present nextFresh nextSlot true offset len nonzero good.2.2.1 nextBounds
  have childWell : (finalTree tree tracker parentTag offset len).locations.WellFormed := geometry.1
  refine ⟨own.1,own.2,?_,childWell,?_⟩
  · have lookup := metadata.lookup
    change (GeneralBorrowFreshMetadataChildSlot.result read.tree parentTag tracker.global.nextPointerTag true offset len).indexOfTag _ = some (GeneralBorrowFreshMetadataChildSlot.index nextSlot) at lookup
    rw [show GeneralBorrowFreshMetadataChildSlot.index nextSlot = GeneralBorrowFreshMetadataChildSlot.index slot from slotEq] at lookup
    exact lookup
  · apply GeneralBorrowFreshActiveWithin.active_on _ _ _ _ _ childWell
    cases slot <;> simpa only [finalTree,GeneralBorrowFreshSharedWithinStages.slot_index,GeneralBorrowFreshMetadataChildSlot.index,
      GeneralBorrowFreshAnchor.sharedState,NestedConstruction.frozenRead,TypedBorrowSteps.registeredGlobal,ite_true] using activity.2.2.2

end DuplicatePrefix.GeneralBorrowForestMixedSharedReleaseData
