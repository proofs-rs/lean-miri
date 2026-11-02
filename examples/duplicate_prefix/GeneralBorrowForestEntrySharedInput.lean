import duplicate_prefix.GeneralBorrowForestEntryReleaseData
import duplicate_prefix.GeneralBorrowForestEntryResources
import duplicate_prefix.GeneralBorrowForestEntryFreshMap
import duplicate_prefix.GeneralBorrowForestEntryVacantClean
import duplicate_prefix.GeneralBorrowForestEntryMixed
import duplicate_prefix.GeneralBorrowFreshSharedWithinStages
namespace DuplicatePrefix.GeneralBorrowForestEntrySharedInput
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open GenericFunctionEntryState
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
structure First (tree : BorrowTree) (protections : ProtectedTags) (tag exprTag helperTag : BorTag)
    (anchor primary : UniIndex) (extras : List UniIndex) (offset len : UInt64) where
  context : GeneralBorrowForestAccessData.Context tree anchor primary extras
  anchorTag : context.anchorNode.tag = tag
  covered : GeneralBorrowGraph.RootsCover tree
  tagPresent : tree.indexOfTag tag = some anchor
  fresh : GeneralBorrowTagMap.Fresh tree.tagMapping exprTag
  helperFresh : GeneralBorrowTagMap.Fresh tree.tagMapping helperTag
  slot : GeneralBorrowFreshReborrowStages.Slot tree context.depth anchor
  clean : GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get (GeneralBorrowFreshMetadataChildSlot.index slot) = none) tree.locations
  vacantClean : GeneralBorrowGcVacantClean.VacantClean tree
  allocator : GeneralBorrowGcAllocator.Invariant tree
  fits : tree.nodes.data.size ≤ 4294967296
  well : tree.locations.WellFormed
  bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat
  room : tree.nodes.size+5 ≤ 4294967295
  owned : GeneralRangeMapOrigins.OwnedOn
    (fun location => Nonempty (GeneralBorrowForestMixedAccess.Data tree location protections anchor primary extras (fun _ => true))) offset (offset+len) tree.locations
  active : GeneralBorrowFreshActiveWithin.ActiveWithin tree anchor .Write offset (offset+len)

def build (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (data : GeneralBorrowForestEntryValidity.Data tree tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get (GeneralBorrowFreshMetadataChildMutableSlot.index data.slot) = none) tree.locations)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (fresh2 : (next tracker fresh).global.nextPointerTag.value < 18446744073709551615)
    (successorFresh : GeneralBorrowProtector.Fresh tree (next tracker fresh).global.nextPointerTag)
    (different : tracker.global.nextPointerTag ≠ (next tracker fresh).global.nextPointerTag)
    (allocator : GeneralBorrowGcAllocator.Invariant tree) (room : tree.nodes.size+6 ≤ 4294967295)
    (vacantClean : GeneralBorrowGcVacantClean.VacantClean tree)
    (exprTag helperTag : BorTag)
    (exprFresh : GeneralBorrowTagMap.Fresh tree.tagMapping exprTag) (exprDifferent : tracker.global.nextPointerTag ≠ exprTag)
    (helperFresh : GeneralBorrowTagMap.Fresh tree.tagMapping helperTag) (helperDifferent : tracker.global.nextPointerTag ≠ helperTag) :
    First (GeneralBorrowForestArgumentCopy.finalTree tree tracker parentTag offset len) (held tracker fresh fresh2).global.protectedTags
      tracker.global.nextPointerTag exprTag helperTag (GeneralBorrowFreshMetadataChildMutableSlot.index data.slot) data.primary data.extras offset len := by
  let registered := TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag
  have registeredData := GeneralBorrowForestMutableRegister.registered tree tracker.global {} ⟨1,by decide⟩
    tracker.global.nextPointerTag .StrongProtector data.parent data.primary data.extras data.tagFresh data.nodeTags
    data.globalUnheld offset (offset+len) data.owned
  have stages := GeneralBorrowForestProtected.run tree registered.protectedTags parentTag tracker.global.nextPointerTag data.parent data.primary data.extras
    offset len .VisitChildrenOfAccessed data.context data.covered data.tagPresent data.tagFresh data.slot data.nodeFits nonzero data.well bounds registeredData.2.2.2
  let after := GeneralBorrowForestArgumentCopy.finalTree tree tracker parentTag offset len
  let index := GeneralBorrowFreshMetadataChildMutableSlot.index data.slot
  have owned : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowForestMutableAccess.Data after location registered.protectedTags index data.primary data.extras))
      offset (offset+len) after.locations := stages.2.2.2.1
  let context := Classical.choice stages.2.2.1
  have tagPresent : after.indexOfTag tracker.global.nextPointerTag = some index := stages.2.2.2.2.1
  have well : after.locations.WellFormed := stages.2.2.2.2.2.1
  have fits : after.nodes.data.size ≤ 4294967296 := stages.2.2.2.2.2.2.2.1
  have within := GeneralBorrowForestEntryActivity.child tree tracker parentTag offset len nonzero data bounds clean
  have future := GeneralBorrowForestEntryFreshness.future tree tracker parentTag offset len nonzero data bounds
    (next tracker fresh).global.nextPointerTag successorFresh different
  have futureNode : ∀ query node, after.nodeAt query = some node → node.tag ≠ (next tracker fresh).global.nextPointerTag := by
    intro query node present
    exact future (query,node) (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get after.nodes query node).mpr present))
  have protectedOwners : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowForestMutableAccess.Data after location (held tracker fresh fresh2).global.protectedTags index data.primary data.extras))
      offset (offset+len) after.locations := by
    intro position valid positive lower upper
    obtain ⟨localData⟩ := owned position valid positive lower upper
    exact ⟨GeneralBorrowForestMutableRegister.protect after _ registered.protectedTags index data.primary data.extras
      (next tracker fresh).global.nextPointerTag .StrongProtector futureNode localData⟩
  let resources := GeneralBorrowForestEntryResources.build tree tracker parentTag offset len nonzero data bounds allocator room
  let depth := GeneralBorrowCanonicalParentDepth.normalize after.nodes context.depth
  let normalized : GeneralBorrowForestAccessData.Context after index data.primary data.extras := {context with depth := depth}
  have aligned := GeneralBorrowFreshStagePool.empty_aligned after resources.allocator.accounting
  have nextRoom : after.nodes.size+5 ≤ 4294967295 := by
    have size := GeneralBorrowForestEntryResources.growth tree tracker parentTag offset len nonzero data bounds allocator
    change after.nodes.size ≤ tree.nodes.size+1 at size
    omega
  have mappingFits : after.tagMapping.deassigned.back? = none → after.tagMapping.mapping.size ≤ 4294967295 := by
    intro empty
    rw [aligned empty]
    change after.nodes.data.size+5 ≤ _ at nextRoom
    omega
  let slot := GeneralBorrowCanonicalParentDepth.slot after context.depth index context.anchorNode context.anchorPresent resources.allocator.pool aligned mappingFits
  have cleanAfter := GeneralBorrowForestEntryVacantClean.preserves tree tracker parentTag offset len nonzero data bounds vacantClean
  exact {
    context := normalized,anchorTag := by
      obtain ⟨node,present,tag,_⟩ := (GeneralBorrowForestEntryMetadata.build tree tracker parentTag offset len nonzero data bounds).node
      have same : context.anchorNode = node := Option.some.inj (context.anchorPresent.symm.trans present)
      exact (congrArg TreeNode.tag same).trans tag,
    covered := stages.2.2.2.2.2.2.2.2,tagPresent := tagPresent,
    fresh := GeneralBorrowForestEntryFreshMap.future tree tracker parentTag offset len nonzero data bounds exprTag exprFresh exprDifferent,
    helperFresh := GeneralBorrowForestEntryFreshMap.future tree tracker parentTag offset len nonzero data bounds helperTag helperFresh helperDifferent,
    slot := slot,clean := cleanAfter _ (GeneralBorrowFreshSharedWithinStages.slot_vacant after depth index slot),
    vacantClean := cleanAfter,allocator := resources.allocator,fits := fits,well := well,
    bounds := by change offset.toNat+len.toNat ≤ after.locations.size.bytes.toNat;rw [(GeneralBorrowForestEntryMetadata.build tree tracker parentTag offset len nonzero data bounds).capacity];exact bounds,
    room := nextRoom,
    owned := GeneralBorrowForestEntryMixed.owned after (held tracker fresh fresh2).global.protectedTags index data.primary data.extras offset (offset+len) protectedOwners,
    active := within }
end
end DuplicatePrefix.GeneralBorrowForestEntrySharedInput
