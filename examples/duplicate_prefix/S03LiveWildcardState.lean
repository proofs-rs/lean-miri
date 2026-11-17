import duplicate_prefix.S03LiveEmptyState
namespace DuplicatePrefix.S03LiveWildcardState
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification
open S03LiveEmptyState (next argumentsMachine)
set_option autoImplicit false
set_option maxRecDepth 65536
noncomputable section
/-- The actual concrete empty argument constructor preserves an original
wildcard return pointer and its raw physical binding. The full observer
capability is the constructor result, rather than a future-input assumption. -/
def input {before : Before} {place : MPlaceTy Provenance}
    (original : DuplicatePrefixReturnPlaceInput.Input before place)
    (fresh : original.tracker.global.nextPointerTag.value < 18446744073709551615)
    (parentTag : BorTag) (slot : ConcreteEmptyPoolEntry.Input original.entry.allocation.extra parentTag original.tracker.global.nextPointerTag)
    (wildcard : original.pointer.provenance = .wildcard)
    (positive : DuplicatePrefixBorrowAuthorization.Positive slot.after (next original.tracker fresh).global.protectedTags
      original.source original.selectedRoot original.maximum original.offset 1) :
    DuplicatePrefixReturnPlaceInput.Input (argumentsMachine original fresh parentTag slot) place := by
  let entry : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
    {original.entry with allocation := original.entry.allocation.setExtra slot.after}
  refine {
    tracker := next original.tracker fresh, enabled := rfl,
    pointer := original.pointer,physicalPointer := original.physicalPointer,layout := original.layout,aligned := original.aligned,
    id := original.id,entry := entry,base := original.base,offset := original.offset,capacity := original.capacity,
    live := ?_,cachedBase := original.cachedBase,pointerAddress := original.pointerAddress,nonnull := original.nonnull,
    addressFits := original.addressFits,bounds := original.bounds,size := original.size,bytes := original.bytes,mutable := original.mutable,
    maskValid := original.maskValid,maskLength := original.maskLength,provenanceMap := original.provenanceMap,
    borrowSize := ?_,source := original.source,selectedRoot := original.selectedRoot,maximum := original.maximum,
    binding := ?_,borrow := positive }
  · exact MemoryCopyBridge.live_lookup_replaced before.memory original.id entry
  · change slot.after.locations.size.bytes = original.capacity
    rw [S04ZeroChildMetadata.capacity _ _ _ slot]
    exact original.borrowSize
  · have binding := original.binding
    simp only [DuplicatePrefixReferenceInput.Binding,wildcard] at binding ⊢
    exact binding

end
end DuplicatePrefix.S03LiveWildcardState
