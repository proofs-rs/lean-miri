import duplicate_prefix.S02SameDestinationCurrent
import duplicate_prefix.S02FnEntryBinding
import duplicate_prefix.GeneralBorrowRawFnEntryResources

namespace DuplicatePrefix.S02SameDestinationInput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2500000
noncomputable section

/-- The actual post-argument machine admits the general same-allocation
return-place Input. Its entry contains the exact FnEntry tree, and its full
Positive and provenance Binding are derived from the original contract. -/
theorem at_actual_current
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (same : id = input.contract.destination.id)
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
    (fresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615) :
    let current := GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
      reference.tracker fresh reference.id reference.entry tag reference.offset len
    let finalTree := GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra reference.tracker tag reference.offset len
    ∃ destination : DuplicatePrefixReturnPlaceInput.Input current place,
      destination.id = input.contract.destination.id ∧
      destination.entry = {input.contract.destination.entry with allocation := input.contract.destination.entry.allocation.setExtra finalTree} ∧
      destination.offset = input.contract.destination.offset ∧ destination.source = input.contract.destination.source ∧
      destination.selectedRoot = input.contract.destination.selectedRoot ∧ destination.maximum = input.contract.destination.maximum := by
  obtain ⟨idEq,raw,parentTag,offsetEq,lenEq,_source,_selected,_maximum,runtime⟩ :=
    S05ConcreteEntryBridge.from_positive id tag address len reference input.contract.runtime input.contract.resources
  let original := input.contract.destination
  let finalTree := GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra reference.tracker tag reference.offset len
  let machine := RawRootInvocation.machine #[] before
  let current := GeneralBorrowRawFnEntryScope.resultMachine machine reference.tracker fresh reference.id reference.entry tag reference.offset len
  have destId : reference.id = original.id := idEq.symm.trans same
  have entryEq : reference.entry = original.entry := by
    have live := reference.live
    rw [destId] at live
    exact congrArg Prod.snd (Option.some.inj (live.symm.trans original.live))
  obtain ⟨positive⟩ := S02SameDestinationCurrent.destination_positive_final_tree id tag address len input nonempty same reference fresh
  have capacity := (GeneralBorrowRawFnEntryResources.resources reference.entry.allocation.extra reference.tracker ({} : FrameState)
    reference.id runtime raw).2.1
  rw [parentTag,offsetEq,lenEq] at capacity
  have oldBinding : DuplicatePrefixReferenceInput.Binding before.user.addresses original.pointer original.id original.base
      original.entry.allocation.byteSize reference.entry.allocation.extra original.source := by
    rw [entryEq]
    exact original.binding
  have binding := S02FnEntryBinding.binding reference.entry.allocation.extra reference.tracker ({} : FrameState) reference.id runtime raw
    before.user.addresses original.pointer original.id original.base original.entry.allocation.byteSize original.source oldBinding
  rw [parentTag,offsetEq,lenEq] at binding
  obtain ⟨memory,_borrow,_race,addresses,_ghost,_shallow,_types,_backend,_extras⟩ := RawRootInvocation.preservation #[] before
  let nextTracker : MachineHooks.BorrowState := ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global fresh,reference.tracker.retagMode⟩
  let entry := {original.entry with allocation := original.entry.allocation.setExtra finalTree}
  let destination : DuplicatePrefixReturnPlaceInput.Input current place := {
    tracker := nextTracker
    enabled := rfl
    pointer := original.pointer
    physicalPointer := original.physicalPointer
    layout := original.layout
    aligned := original.aligned
    id := original.id
    entry := entry
    base := original.base
    offset := original.offset
    capacity := original.capacity
    live := by
      change (RetagEntry.updatedMemory machine.memory reference.id reference.entry finalTree).live.find?
        (fun row => row.1 == original.id) = some (original.id,entry)
      rw [←destId]
      change (RetagEntry.updatedMemory machine.memory reference.id reference.entry finalTree).live.find?
        (fun row => row.1 == reference.id) = some (reference.id,{original.entry with allocation := original.entry.allocation.setExtra finalTree})
      rw [←entryEq]
      exact MemoryCopyBridge.live_lookup_replaced machine.memory reference.id _
    cachedBase := by
      change machine.user.addresses.baseAddr.find? (fun row => row.allocId == original.id) = _
      rw [addresses]
      exact original.cachedBase
    pointerAddress := original.pointerAddress
    nonnull := original.nonnull
    addressFits := original.addressFits
    bounds := original.bounds
    size := original.size
    bytes := original.bytes
    mutable := original.mutable
    maskValid := original.maskValid
    maskLength := original.maskLength
    provenanceMap := original.provenanceMap
    borrowSize := by
      change finalTree.locations.size.bytes = original.capacity
      rw [capacity,entryEq]
      exact original.borrowSize
    source := original.source
    selectedRoot := original.selectedRoot
    maximum := original.maximum
    binding := by
      change DuplicatePrefixReferenceInput.Binding machine.user.addresses original.pointer original.id original.base
        original.entry.allocation.byteSize finalTree original.source
      rw [addresses]
      exact binding
    borrow := positive }
  exact ⟨destination,rfl,rfl,rfl,rfl,rfl,rfl⟩

end
end DuplicatePrefix.S02SameDestinationInput

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02SameDestinationInput.at_actual_current) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
