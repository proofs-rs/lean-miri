import duplicate_prefix.GeneralBorrowForestMixedSharedReleaseData
import duplicate_prefix.GeneralBorrowFreshSharedSlotPaths
import duplicate_prefix.GeneralBorrowFreshSharedStagePaths
namespace DuplicatePrefix.GeneralBorrowForestMixedSharedAttach
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestMixedSharedArgumentCopy
open BorrowRangeAccess GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
theorem attach
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
    (owned : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowForestMixedAccess.Data tree location tracker.global.protectedTags parent primary extras writable))
      offset (offset+len) tree.locations)
    (oldLocation newLocation : LocationTree) (tags : ProtectedTags) :
    GeneralBorrowFreshSharedPaths.Attach (source_normal_projection tree oldLocation tags).topology
      (source_normal_projection (finalTree tree tracker parentTag offset len) newLocation tags).topology
      parent.toNat (GeneralBorrowFreshMetadataChildSlot.index slot).toNat := by
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
  have forest : GeneralBorrowForest.Forest (source_normal_projection tree oldLocation tags).topology := by
    apply Classical.choice
    have lenNat : 0 < len.toNat := by
      have nz : len.toNat ≠ 0 := fun zero => nonzero (UInt64.toNat_inj.mp (by simpa using zero))
      omega
    have addition : (offset+len).toNat = offset.toNat+len.toNat := by
      rw [UInt64.toNat_add,Nat.mod_eq_of_lt (by have bound := UInt64.toNat_lt_size tree.locations.size.bytes; change tree.locations.size.bytes.toNat < 18446744073709551616 at bound;omega)]
    have inside : offset.toNat < tree.locations.size.bytes.toNat := by omega
    obtain ⟨position,valid,lower,upper⟩ := GeneralRangeMapGeometry.covered tree.locations well offset inside
    obtain ⟨data⟩ := owned position valid (by omega) (by omega) upper
    rw [←GeneralBorrowFreshSharedStagePaths.topology_any tree tree.locations.entries[position].data oldLocation tracker.global.protectedTags tags]
    exact ⟨data.base.forest⟩
  have topology := GeneralBorrowFreshMetadataChildAllocator.topology_frame tree read.tree nodes oldLocation oldLocation tags
  have forestRead : GeneralBorrowForest.Forest (source_normal_projection read.tree oldLocation tags).topology := by
    rw [topology];exact forest
  have attached := GeneralBorrowFreshSharedSlotPaths.attach read.tree depth nextChildren nextCovered parentTag tracker.global.nextPointerTag
    parent context.anchorNode nextTag present nextFresh nextSlot true offset len nonzero good.2.2.1 nextBounds oldLocation newLocation tags forestRead
  rw [topology] at attached
  change GeneralBorrowFreshSharedPaths.Attach _ _ parent.toNat (GeneralBorrowFreshMetadataChildSlot.index nextSlot).toNat at attached
  rw [show GeneralBorrowFreshMetadataChildSlot.index nextSlot = GeneralBorrowFreshMetadataChildSlot.index slot from slotEq] at attached
  exact attached

end DuplicatePrefix.GeneralBorrowForestMixedSharedAttach
