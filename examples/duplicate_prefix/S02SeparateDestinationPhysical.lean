import duplicate_prefix.S02SeparateDestinationMetadata
import duplicate_prefix.S03FinalReturnInputBounds

namespace DuplicatePrefix.S02SeparateDestinationPhysical
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open S03FinalReturnInputBounds
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The actual uninit result has the physical concrete-return packet needed by
the relaxed final Return theorem. Full post-clear provenance ordering is not
needed: the real clear operation supplies current pointer bounds. -/
def of_protection {before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser}
    {place : MPlaceTy Provenance} (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (tag : BorTag) (concrete : input.pointer.provenance = .concrete input.id tag)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (fresh : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (tree : BorrowTree) (updated : Allocation Provenance BorrowTree) (written : BorrowTree)
    (extra : updated.extra = written)
    (bytes : updated.byteSize = input.entry.allocation.byteSize)
    (length : updated.len = input.entry.allocation.len) (mutable : updated.mutability = .Mut)
    (maskWf : InitMaskCopy.WellFormed updated.initializationMask)
    (maskLen : updated.initializationMask.len = input.entry.allocation.initializationMask.len)
    (pointers : ∀ row ∈ updated.provenanceMap.ptrs, row.1.bytes.toNat+8≤updated.len)
    (capacity : written.locations.size = input.entry.allocation.extra.locations.size)
    (parentPreserved : written.indexOfTag tag = input.entry.allocation.extra.indexOfTag tag) :
    Destination (S04ProtectUninit.finished before place input frames frame borrowFrame fresh tree updated).machine place := by
  have binding := input.binding
  simp only [DuplicatePrefixReferenceInput.Binding,concrete] at binding
  let parent := Classical.choose binding.2
  have tagged := (Classical.choose_spec binding.2).2
  let state := S04ProtectUninit.finished before place input frames frame borrowFrame fresh tree updated
  refine {
    pointer := input.pointer, physicalPointer := input.physicalPointer, layout := input.layout, aligned := input.aligned,
    id := input.id, entry := {input.entry with allocation := updated}, base := input.base, offset := input.offset,
    capacity := input.capacity, live := ?_, cachedBase := input.cachedBase, pointerAddress := input.pointerAddress,
    nonnull := input.nonnull, addressFits := input.addressFits, bounds := input.bounds,
    size := bytes.trans input.size, bytes := length.trans input.bytes, mutable := mutable,
    maskValid := maskWf, maskLength := maskLen.trans input.maskLength, pointerBounds := pointers,
    borrowSize := ?_, tag := tag, parent := parent, concrete := concrete, tagged := ?_ }
  · exact MemoryCopyBridge.live_lookup_replaced
      (ReturnProtection.borrowedState frames frame borrowFrame before input.tracker fresh input.id input.entry tree).machine.memory
      input.id {input.entry with allocation := updated}
  · rw [extra]
    change written.locations.size.bytes = input.capacity
    rw [capacity]
    exact input.borrowSize
  · change updated.extra.indexOfTag tag = some parent
    rw [extra]
    rw [parentPreserved]
    exact tagged

end
end DuplicatePrefix.S02SeparateDestinationPhysical

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationPhysical.of_protection) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate destination physical dependency {dependency}"
