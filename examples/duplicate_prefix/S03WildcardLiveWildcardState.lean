import duplicate_prefix.S03WildcardLiveState

namespace DuplicatePrefix.S03WildcardLiveWildcardState
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification S03WildcardLiveState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section
/-- The actual hidden zero root preserves original wildcard return binding
and every byte/address field while changing the original allocation's tree. -/
def input {before : Before} {place : MPlaceTy Provenance}
    (original : DuplicatePrefixReturnPlaceInput.Input before place)
    (fresh : original.tracker.global.nextPointerTag.value < 18446744073709551615)
    (rootSlot : WildcardHitPoolRoot.Slot original.entry.allocation.extra)
    (wildcard : original.pointer.provenance = .wildcard)
    (positive : DuplicatePrefixBorrowAuthorization.Positive (rootSlot.after original.tracker.global.nextPointerTag)
      (next original.tracker fresh).global.protectedTags original.source original.selectedRoot original.maximum original.offset 1) :
    DuplicatePrefixReturnPlaceInput.Input (argumentsMachine original fresh rootSlot) place := by
  let tree := rootSlot.after original.tracker.global.nextPointerTag
  let entry : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
    {original.entry with allocation := original.entry.allocation.setExtra tree}
  refine {
    tracker := next original.tracker fresh, enabled := rfl,
    pointer := original.pointer,physicalPointer := original.physicalPointer,layout := original.layout,aligned := original.aligned,
    id := original.id,entry := entry,base := original.base,offset := original.offset,capacity := original.capacity,
    live := ?_,cachedBase := original.cachedBase,pointerAddress := original.pointerAddress,nonnull := original.nonnull,
    addressFits := original.addressFits,bounds := original.bounds,size := original.size,bytes := original.bytes,mutable := original.mutable,
    maskValid := original.maskValid,maskLength := original.maskLength,provenanceMap := original.provenanceMap,
    borrowSize := original.borrowSize,source := original.source,selectedRoot := original.selectedRoot,maximum := original.maximum,
    binding := ?_,borrow := positive }
  · exact MemoryCopyBridge.live_lookup_replaced before.memory original.id entry
  · change DuplicatePrefixReferenceInput.Binding _ original.pointer _ _ _ tree original.source
    have binding := original.binding
    simp only [DuplicatePrefixReferenceInput.Binding,wildcard] at binding ⊢
    exact binding

end
end DuplicatePrefix.S03WildcardLiveWildcardState
