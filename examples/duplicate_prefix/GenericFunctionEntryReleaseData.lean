import duplicate_prefix.GenericFunctionEntryBundle
import duplicate_prefix.GenericAsMutReleasePlan
namespace DuplicatePrefix.GenericFunctionEntryReleaseData
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open GenericFunctionEntryState
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- The actual root argument child has generic release data even after the
independent return-slot protector is registered. All inputs concern the initial
buffer tree, allocator slot and issued tags; no operation outcome is assumed. -/
theorem prepare
    (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (data : GenericAsMutPtrEntryValidity.Data tree tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree =>
      location.perms.get (GeneralBorrowFreshMutableStages.slot_index data.slot) = none) tree.locations)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (fresh2 : (next tracker fresh).global.nextPointerTag.value < 18446744073709551615)
    (successorFresh : GeneralBorrowProtector.Fresh tree (next tracker fresh).global.nextPointerTag)
    (different : tracker.global.nextPointerTag ≠ (next tracker fresh).global.nextPointerTag)
    (positive : offset.toNat < (offset+len).toNat) :
    let after := GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len
    ∃ release : GenericAsMutReleasePlan.Input after (held tracker fresh fresh2).global.protectedTags tracker.global.nextPointerTag,
      release.anchor=GeneralBorrowFreshMutableStages.slot_index data.slot ∧ release.lower=offset ∧ release.upper=offset+len := by
  let after := GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len
  obtain ⟨metadata⟩ : Nonempty (GenericFunctionEntryMetadata.Output tree tracker parentTag offset len data) :=
    ⟨GenericFunctionEntryMetadata.build tree tracker parentTag offset len nonzero data bounds⟩
  obtain ⟨node,present,tag,notExposed⟩ := metadata.node
  have ownership := GenericFunctionEntryOwnership.child tree tracker parentTag offset len nonzero data bounds clean
  have future := (GenericFunctionEntryFreshness.future tree tracker parentTag offset len nonzero data bounds
    (next tracker fresh).global.nextPointerTag successorFresh different).2
  have owned := GeneralBorrowFreshReadFrame.protector_owned_on after
    (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags
    (next tracker fresh).global.nextPointerTag .StrongProtector future
    (GeneralBorrowFreshMutableStages.slot_index data.slot) .Write offset (offset+len) ownership.1
  let release : GenericAsMutReleasePlan.Input after (held tracker fresh fresh2).global.protectedTags tracker.global.nextPointerTag := {
    anchor := GeneralBorrowFreshMutableStages.slot_index data.slot
    root := data.root
    lower := offset
    upper := offset+len
    positive := positive
    fits := metadata.nodeFits
    depth := metadata.certificates.depth
    children := metadata.certificates.children
    node := node
    anchorPresent := present
    notExposed := notExposed
    roots := metadata.roots
    covered := metadata.certificates.covered
    tagPresent := metadata.lookup
    well := metadata.well
    within := ownership.2
    owned := owned }
  exact ⟨release,rfl,rfl,rfl⟩
end DuplicatePrefix.GenericFunctionEntryReleaseData
