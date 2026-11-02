import duplicate_prefix.S03ReturnWildcardProtectionRaw
import duplicate_prefix.S04FinalReturnWildcardInput

namespace DuplicatePrefix.S03ReturnWildcardMetadata
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- Form the permission-free original wildcard destination on the ACTUAL
protection/uninit result. Only metadata derived by that operation is supplied;
full provenance-map well-formedness after clear is unnecessary. -/
def of_protection {before : DuplicatePrefixCallSpecification.Before} {place : MPlaceTy Provenance}
    (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (wildcard : input.pointer.provenance = .wildcard)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (fresh : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (tree : BorrowTree) (updated : Allocation Provenance BorrowTree) (written : BorrowTree)
    (extra : updated.extra = written)
    (bytes : updated.byteSize = input.entry.allocation.byteSize)
    (length : updated.len = input.entry.allocation.len) (mutable : updated.mutability = .Mut)
    (maskWf : InitMaskCopy.WellFormed updated.initializationMask)
    (maskLen : updated.initializationMask.len = input.entry.allocation.initializationMask.len)
    (pointers : ∀ row ∈ updated.provenanceMap.ptrs, row.1.bytes.toNat+8≤updated.len)
    (capacity : written.locations.size = input.entry.allocation.extra.locations.size) :
    S04FinalReturnWildcardInput.Destination
      (S04ProtectUninit.finished before place input frames frame borrowFrame fresh tree updated).machine place := by
  have binding := input.binding
  simp only [DuplicatePrefixReferenceInput.Binding,wildcard] at binding
  obtain ⟨source,mode,exposed,geometry⟩ := binding
  let state := S04ProtectUninit.finished before place input frames frame borrowFrame fresh tree updated
  refine {
    pointer := input.pointer, physicalPointer := input.physicalPointer, layout := input.layout, aligned := input.aligned,
    id := input.id, entry := {input.entry with allocation := updated}, base := input.base, offset := input.offset,
    capacity := input.capacity, live := ?_, cachedBase := input.cachedBase, pointerAddress := input.pointerAddress,
    nonnull := input.nonnull, addressFits := input.addressFits, bounds := input.bounds,
    size := bytes.trans input.size, bytes := length.trans input.bytes, mutable := mutable,
    maskValid := maskWf, maskLength := maskLen.trans input.maskLength, pointerBounds := pointers,
    borrowSize := ?_, wildcard := wildcard, mode := mode, exposed := exposed, geometry := ?_ }
  · exact MemoryCopyBridge.live_lookup_replaced
      (ReturnProtection.borrowedState frames frame borrowFrame before input.tracker fresh input.id input.entry tree).machine.memory
      input.id {input.entry with allocation := updated}
  · rw [extra]
    change written.locations.size.bytes = input.capacity
    rw [capacity]
    exact input.borrowSize
  · change WildcardGeneralHitReborrow.Geometry before.user.addresses.intToPtrMap input.pointer.offset.bytes
      input.base input.id updated.byteSize
    rw [bytes]
    exact geometry

/-- Tree-only body updates preserve every physical field required by final
wildcard copy. Address equality and exact live lookup come from the actual
body transition; no permission or successful final access is a premise. -/
def after_tree {before after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser}
    {place : MPlaceTy Provenance} (destination : S04FinalReturnWildcardInput.Destination before place)
    (tree : BorrowTree)
    (addresses : after.user.addresses = before.user.addresses)
    (live : after.memory.live.find? (fun row => row.1 == destination.id) =
      some (destination.id,{destination.entry with allocation := destination.entry.allocation.setExtra tree}))
    (capacity : tree.locations.size = destination.entry.allocation.extra.locations.size) :
    S04FinalReturnWildcardInput.Destination after place := by
  refine {
    pointer := destination.pointer, physicalPointer := destination.physicalPointer,
    layout := destination.layout, aligned := destination.aligned,
    id := destination.id, entry := {destination.entry with allocation := destination.entry.allocation.setExtra tree},
    base := destination.base, offset := destination.offset, capacity := destination.capacity, live := live,
    cachedBase := ?_, pointerAddress := destination.pointerAddress, nonnull := destination.nonnull,
    addressFits := destination.addressFits, bounds := destination.bounds, size := destination.size, bytes := destination.bytes,
    mutable := destination.mutable, maskValid := destination.maskValid, maskLength := destination.maskLength,
    pointerBounds := destination.pointerBounds, borrowSize := ?_, wildcard := destination.wildcard,
    mode := ?_, exposed := ?_, geometry := ?_ }
  · rw [addresses];exact destination.cachedBase
  · change tree.locations.size.bytes = destination.capacity
    rw [capacity];exact destination.borrowSize
  · rw [addresses];exact destination.mode
  · rw [addresses];exact destination.exposed
  · rw [addresses];exact destination.geometry

end
end DuplicatePrefix.S03ReturnWildcardMetadata
