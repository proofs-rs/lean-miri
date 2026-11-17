import duplicate_prefix.S04ReturnProtection

namespace DuplicatePrefix.S04ReturnRetaggedInput
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- The memory/borrow-tracker projection of a retag keeps the backing bytes and
address map. This definition records the state consumed by the ensuing write. -/
def installed (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tree : BorrowTree) :=
  {before with
    memory := RetagEntry.updatedMemory before.memory id entry tree
    borrowTracker := some tracker}

/-- Reuse the initial destination's physical metadata for the new concrete
retagged pointer. Only the actual new tree's tag binding and byte capability
need to be supplied by the retag theorem; no write success is assumed here. -/
def from_tree {before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser}
    {place : MPlaceTy Provenance} (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (tracker : MachineHooks.BorrowState) (tree : BorrowTree) (tag : BorTag)
    (child : UniIndex) (selected : Option UniIndex) (maximum : Option BorTag)
    (tagged : tree.indexOfTag tag = some child)
    (size : tree.locations.size = input.entry.allocation.extra.locations.size)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree tracker.global.protectedTags
      (some child) selected maximum input.offset 1) :
    DuplicatePrefixReturnPlaceInput.Input
      (installed before tracker input.id input.entry tree)
      (TypedRetagGeneric.retaggedPlace place input.id tag) := by
  let pointer : Pointer Provenance := ⟨input.pointer.offset,.concrete input.id tag⟩
  let entry : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
    {input.entry with allocation := input.entry.allocation.setExtra tree}
  refine {
    tracker := tracker, enabled := rfl,
    pointer := pointer, physicalPointer := ?_, layout := input.layout, aligned := input.aligned,
    id := input.id, entry := entry, base := input.base, offset := input.offset, capacity := input.capacity,
    live := ?_, cachedBase := input.cachedBase, pointerAddress := input.pointerAddress,
    nonnull := input.nonnull, addressFits := input.addressFits, bounds := input.bounds,
    size := input.size, bytes := input.bytes, mutable := input.mutable,
    maskValid := input.maskValid, maskLength := input.maskLength, provenanceMap := input.provenanceMap,
    borrowSize := ?_, source := some child, selectedRoot := selected, maximum := maximum,
    binding := ?_, borrow := positive }
  · simp only [TypedRetagGeneric.retaggedPlace, input.physicalPointer, pointer, Pointer.withOptionalProvenance]
  · exact MemoryCopyBridge.live_lookup_replaced before.memory input.id entry
  · change tree.locations.size.bytes = input.capacity
    rw [size]
    exact input.borrowSize
  · exact ⟨rfl,child,rfl,tagged⟩

/-- The metadata bridge applies to the exact state returned by the configured
retag proof, including its real updated memory and borrow tracker. -/
def from_borrowed {before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser}
    {place : MPlaceTy Provenance} (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (fresh : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (tree : BorrowTree) (child : UniIndex) (selected : Option UniIndex) (maximum : Option BorTag)
    (tagged : tree.indexOfTag input.tracker.global.nextPointerTag = some child)
    (size : tree.locations.size = input.entry.allocation.extra.locations.size)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree
      (TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker input.tracker fresh)
        input.tracker.global.nextPointerTag).protectedTags (some child) selected maximum input.offset 1) :
    DuplicatePrefixReturnPlaceInput.Input
      (ReturnProtection.borrowedState frames frame borrowFrame before input.tracker fresh input.id input.entry tree).machine
      (TypedRetagGeneric.retaggedPlace place input.id input.tracker.global.nextPointerTag) :=
  from_tree input
    (TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker input.tracker fresh)
      input.tracker.global.nextPointerTag) tree input.tracker.global.nextPointerTag child selected maximum tagged size positive

end DuplicatePrefix.S04ReturnRetaggedInput
