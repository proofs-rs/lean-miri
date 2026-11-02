import duplicate_prefix.GeneralBorrowForestEntryActivity
import duplicate_prefix.GeneralBorrowForestEntryFreshness
import duplicate_prefix.GeneralBorrowForestReleaseData
import duplicate_prefix.GenericFunctionEntryState

namespace DuplicatePrefix.GeneralBorrowForestEntryReleaseData
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open GenericFunctionEntryState
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Original multiple-root mutable input plus INITIAL selected-slot Clean form
actual ROOT-child release data after both argument and independent return-slot
registrations. All reads, constructors, activity, next metadata and permission
records are derived; no intermediate release Data/Plan/success is a premise. -/
theorem prepare (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (data : GeneralBorrowForestEntryValidity.Data tree tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree =>
      location.perms.get (GeneralBorrowFreshMetadataChildMutableSlot.index data.slot) = none) tree.locations)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (fresh2 : (next tracker fresh).global.nextPointerTag.value < 18446744073709551615)
    (successorFresh : GeneralBorrowProtector.Fresh tree (next tracker fresh).global.nextPointerTag)
    (different : tracker.global.nextPointerTag ≠ (next tracker fresh).global.nextPointerTag)
    (positive : offset.toNat < (offset+len).toNat) :
    let after := GeneralBorrowForestArgumentCopy.finalTree tree tracker parentTag offset len
    ∃ release : GeneralBorrowForestReleaseData.Input after (held tracker fresh fresh2).global.protectedTags tracker.global.nextPointerTag,
      release.anchor = GeneralBorrowFreshMetadataChildMutableSlot.index data.slot ∧ release.lower = offset ∧ release.upper = offset+len := by
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
  obtain ⟨context⟩ : Nonempty (GeneralBorrowForestAccessData.Context after index data.primary data.extras) := stages.2.2.1
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
  let release : GeneralBorrowForestReleaseData.Input after (held tracker fresh fresh2).global.protectedTags tracker.global.nextPointerTag := {
    anchor := index
    primary := data.primary
    extras := data.extras
    context := context
    lower := offset
    upper := offset+len
    positive := positive
    fits := fits
    tagPresent := tagPresent
    well := well
    within := within
    owned := protectedOwners }
  exact ⟨release,rfl,rfl,rfl⟩

end DuplicatePrefix.GeneralBorrowForestEntryReleaseData
