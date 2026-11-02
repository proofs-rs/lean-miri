import duplicate_prefix.S02SeparateDestinationTransport
import duplicate_prefix.GeneralBorrowFreshRegistration

namespace DuplicatePrefix.S02SeparateDestinationAuthorization
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- A source argument's newly registered fresh tag cannot change the
destination tree's preexisting permissions: all present destination nodes
have older tags. This applies to the general multi-root destination tree. -/
theorem destination_positive_after_registration
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {argument : DuplicatePrefixSliceArgument.Argument} {len : UInt64}
    {place : MPlaceTy Provenance}
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before argument len place)
    (fresh : input.contract.tracker.global.nextPointerTag.value < 18446744073709551615) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Positive
      input.contract.destination.entry.allocation.extra
      (TypedRetagGeneric.protectedGlobal input.contract.tracker.global fresh).protectedTags
      input.contract.destination.source input.contract.destination.selectedRoot
      input.contract.destination.maximum input.contract.destination.offset 1) := by
  let destination := input.contract.destination
  have trackerEq : destination.tracker = input.contract.tracker :=
    Option.some.inj (destination.enabled.symm.trans input.contract.runtime.enabled)
  have member : (destination.id,destination.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some destination.live)
  have runtime : DuplicatePrefixBorrowContract.RuntimeFacts destination.entry.allocation.extra
      input.contract.tracker.global := {
    formed := input.contract.runtime.formed (destination.id,destination.entry) member
    coherent := input.contract.runtime.coherent (destination.id,destination.entry) member
    possible := input.contract.runtime.possible (destination.id,destination.entry) member
    below := input.contract.resources.tagsBelow (destination.id,destination.entry) member }
  have complete := GeneralBorrowForestTagHighWater.complete _ _ _ runtime.below
    runtime.formed.allocator.nodeTags
  obtain ⟨_,nodeFresh,_⟩ := GenericFunctionTagFormation.fresh_above
    destination.entry.allocation.extra input.contract.tracker.global.protectedTags
    input.contract.tracker.global.nextPointerTag input.contract.tracker.global.nextPointerTag
    complete (Nat.le_refl _)
  have borrow := destination.borrow
  rw [trackerEq] at borrow
  simpa only [TypedRetagGeneric.protectedGlobal] using
    GeneralBorrowFreshRegistration.positive destination.entry.allocation.extra
      input.contract.tracker.global.protectedTags input.contract.tracker.global.nextPointerTag
      .StrongProtector nodeFresh destination.source destination.selectedRoot
      destination.maximum destination.offset 1 borrow

/-- In the distinct-allocation case, the real post-argument machine admits a
freshly constructed return-place Input. The construction carries the original
destination's physical data and transports its borrow authorization through
the argument's new global protector. It does not assume a future return
protection outcome. -/
theorem destination_input_after_argument
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (different : id ≠ input.contract.destination.id) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
      (fresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615),
      let machine := RawRootInvocation.machine #[] before
      let current := GeneralBorrowRawFnEntryScope.resultMachine machine reference.tracker fresh
        reference.id reference.entry tag reference.offset len
      let root := RawRootInvocation.root before place input.contract.model.noDataRace
      let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
          (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
      let cfg := PreparedContracts.actualConfig options () (remaining+1) span
      (ExecutionMachine.callHooks cfg limits).withRetagMode () .FnEntry
        (RootCallCore.argumentBody (ExecutionMachine.callHooks cfg limits)
          (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
            (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len)
          (EmptyRootArguments.second count))
        (Storage.withCurrent #[] root.frame machine) =
        .ok (2,2) (Storage.withCurrent #[]
          (RootArgumentsTwo.result
            (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
              reference.id reference.tracker.global.nextPointerTag) count).frame current) ∧
      ∃ destination : DuplicatePrefixReturnPlaceInput.Input current place,
        destination.id = input.contract.destination.id ∧
        destination.entry = input.contract.destination.entry ∧
        destination.offset = input.contract.destination.offset := by
  obtain ⟨reference,fresh,actual⟩ := S02ConcreteArgumentScope.argument_body
    id tag address len count input nonempty
  let original := input.contract.destination
  let machine := RawRootInvocation.machine #[] before
  let current := GeneralBorrowRawFnEntryScope.resultMachine machine reference.tracker fresh
    reference.id reference.entry tag reference.offset len
  have idEq : id = reference.id := by
    have binding := reference.binding
    simp only [DuplicatePrefixReferenceInput.Binding,Pointer.new] at binding
    exact binding.1
  have other : reference.id ≠ original.id := idEq ▸ different
  have trackerEq : reference.tracker = input.contract.tracker :=
    Option.some.inj (reference.enabled.symm.trans input.contract.runtime.enabled)
  have fresh' : input.contract.tracker.global.nextPointerTag.value < 18446744073709551615 := by
    simpa only [←trackerEq] using fresh
  have capability := destination_positive_after_registration input fresh'
  have currentCapability : Nonempty (DuplicatePrefixBorrowAuthorization.Positive
      original.entry.allocation.extra
      (TypedRetagGeneric.protectedGlobal reference.tracker.global fresh).protectedTags
      original.source original.selectedRoot original.maximum original.offset 1) := by
    simpa only [←trackerEq] using capability
  obtain ⟨currentCapability⟩ := currentCapability
  have preserved := RawRootInvocation.preservation #[] before
  obtain ⟨memory,_,_,addresses,_,_,_,_,_⟩ := preserved
  let nextTracker : MachineHooks.BorrowState :=
    ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global fresh,reference.tracker.retagMode⟩
  let destination : DuplicatePrefixReturnPlaceInput.Input current place := {
    tracker := nextTracker
    enabled := rfl
    pointer := original.pointer
    physicalPointer := original.physicalPointer
    layout := original.layout
    aligned := original.aligned
    id := original.id
    entry := original.entry
    base := original.base
    offset := original.offset
    capacity := original.capacity
    live := by
      change (RetagEntry.updatedMemory machine.memory reference.id reference.entry
        (GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra reference.tracker
          tag reference.offset len)).live.find? (fun row => row.1 == original.id) = _
      rw [S02SeparateDestinationTransport.other_live machine.memory reference.id original.id reference.entry _ other]
      rw [memory]
      exact original.live
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
    borrowSize := original.borrowSize
    source := original.source
    selectedRoot := original.selectedRoot
    maximum := original.maximum
    binding := by
      change DuplicatePrefixReferenceInput.Binding machine.user.addresses original.pointer original.id
        original.base original.entry.allocation.byteSize original.entry.allocation.extra original.source
      rw [addresses]
      exact original.binding
    borrow := currentCapability }
  exact ⟨reference,fresh,actual,destination,rfl,rfl,rfl⟩

end
end DuplicatePrefix.S02SeparateDestinationAuthorization

open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S02SeparateDestinationAuthorization.destination_positive_after_registration,
      ``DuplicatePrefix.S02SeparateDestinationAuthorization.destination_input_after_argument] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
