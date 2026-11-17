import duplicate_prefix.GenericFunctionEntryFreshness
import duplicate_prefix.GenericFunctionEntryState

namespace DuplicatePrefix.GenericFunctionEntryBundle
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GenericFunctionEntryState
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

set_option autoImplicit false in
/-- Initial buffer ownership, allocator cleanliness and future-tag freshness
supply the buffer facts at the actual entered machine. The distinct return slot's
updated allocation is arbitrary: no operation success or poststate ownership is
assumed. The runtime entry theorem retains its original, weaker input contract. -/
theorem prepare
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (buffer : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (parentTag : BorTag)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (data : GenericAsMutPtrEntryValidity.Data entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree =>
      location.perms.get (GeneralBorrowFreshMutableStages.slot_index data.slot) = none) entry.allocation.extra.locations)
    (fresh2 : (next tracker fresh).global.nextPointerTag.value < 18446744073709551615)
    (successorFresh : GeneralBorrowProtector.Fresh entry.allocation.extra (next tracker fresh).global.nextPointerTag)
    (different : tracker.global.nextPointerTag ≠ (next tracker fresh).global.nextPointerTag)
    (slot : AllocId) (slotEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (slotRoot : BorTag)
    (updated : Allocation Provenance BorrowTree) (separate : buffer ≠ slot) :
    let tree := GenericAsMutPtrArgumentCopy.finalTree entry.allocation.extra tracker parentTag offset len
    let index := GeneralBorrowFreshMutableStages.slot_index data.slot
    let finalMachine := enteredMachine machine tracker fresh buffer entry parentTag offset len fresh2 slot slotEntry slotRoot updated
    ∃ metadata : GenericFunctionEntryMetadata.Output entry.allocation.extra tracker parentTag offset len data,
      finalMachine.memory.live.find? (fun row => row.1 == buffer) =
        some (buffer,{entry with allocation := entry.allocation.setExtra tree}) ∧
      finalMachine.borrowTracker = some (held tracker fresh fresh2) ∧
      GeneralRangeMapOrigins.OwnedOn
        (GeneralBorrowRange.LocationOwned tree (held tracker fresh fresh2).global.protectedTags index .Write)
        offset (offset+len) tree.locations ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin tree index .Write offset (offset+len) ∧
      (∀ future, GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping future →
        GeneralBorrowProtector.Fresh entry.allocation.extra future → tracker.global.nextPointerTag ≠ future →
        GeneralBorrowTagMap.Fresh tree.tagMapping future ∧ GeneralBorrowProtector.Fresh tree future) := by
  let tree := GenericAsMutPtrArgumentCopy.finalTree entry.allocation.extra tracker parentTag offset len
  let index := GeneralBorrowFreshMutableStages.slot_index data.slot
  have child := GenericFunctionEntryOwnership.child entry.allocation.extra tracker parentTag offset len nonzero data bounds clean
  have successor := (GenericFunctionEntryFreshness.future entry.allocation.extra tracker parentTag offset len nonzero data bounds
    (next tracker fresh).global.nextPointerTag successorFresh different).2
  have owned := GeneralBorrowFreshReadFrame.protector_owned_on tree
    (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags
    (next tracker fresh).global.nextPointerTag .StrongProtector successor index .Write offset (offset+len) child.1
  refine ⟨GenericFunctionEntryMetadata.build entry.allocation.extra tracker parentTag offset len nonzero data bounds,
    buffer_lookup machine tracker fresh buffer entry parentTag offset len fresh2 slot slotEntry slotRoot updated separate,
    rfl,owned,child.2,?_⟩
  intro future mapFresh nodeFresh different
  have result := GenericFunctionEntryFreshness.future entry.allocation.extra tracker parentTag offset len nonzero data bounds
    future nodeFresh different
  exact ⟨result.1 mapFresh,result.2⟩

end DuplicatePrefix.GenericFunctionEntryBundle
