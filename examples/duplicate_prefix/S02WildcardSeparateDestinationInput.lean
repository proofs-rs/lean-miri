import duplicate_prefix.S02WildcardArgumentScope
import duplicate_prefix.S02SeparateDestinationAuthorization

namespace DuplicatePrefix.S02WildcardSeparateDestinationInput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- After the real positive wildcard typed argument, a destination in a
different allocation retains its physical row and a Positive borrow packet
under the newly registered source protector. The inequality is a case guard
on the derived allocation id, not a global caller restriction. -/
theorem destination_input_after_argument
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new .wildcard (Size.ofBytes address)) len)
      (output : GeneralBorrowForestFnEntry.Output)
      (fresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615),
      let machine := RawRootInvocation.machine #[] before
      let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine machine reference.tracker fresh
        reference.id reference.entry output.child.tree
      let root := RawRootInvocation.root before place input.contract.model.noDataRace
      let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
          (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
      let cfg := PreparedContracts.actualConfig options () (remaining+1) span
      GeneralBorrowRawWildcardFnEntryRuntime.operation reference.entry.allocation.extra
        reference.tracker.global ({} : FrameState) reference.id reference.offset len = .ok output ∧
      (ExecutionMachine.callHooks cfg limits).withRetagMode () .FnEntry
        (RootCallCore.argumentBody (ExecutionMachine.callHooks cfg limits)
          (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
            (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len)
          (EmptyRootArguments.second count))
        (Storage.withCurrent #[] root.frame machine) =
        .ok (2,2) (Storage.withCurrent #[]
          (RootArgumentsTwo.result
            (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
              reference.id reference.tracker.global.nextPointerTag) count).frame current) ∧
      (reference.id ≠ input.contract.destination.id →
        ∃ destination : DuplicatePrefixReturnPlaceInput.Input current place,
          destination.id = input.contract.destination.id ∧
          destination.entry = input.contract.destination.entry ∧
          destination.offset = input.contract.destination.offset) := by
  obtain ⟨reference,output,fresh,run,actual⟩ :=
    S02WildcardArgumentScope.argument_body address len count input nonempty
  let original := input.contract.destination
  let machine := RawRootInvocation.machine #[] before
  let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine machine reference.tracker fresh
    reference.id reference.entry output.child.tree
  refine ⟨reference,output,fresh,run,actual,?_⟩
  intro other
  have trackerEq : reference.tracker = input.contract.tracker :=
    Option.some.inj (reference.enabled.symm.trans input.contract.runtime.enabled)
  have fresh' : input.contract.tracker.global.nextPointerTag.value < 18446744073709551615 := by
    simpa only [←trackerEq] using fresh
  obtain ⟨currentCapability⟩ :=
    S02SeparateDestinationAuthorization.destination_positive_after_registration input fresh'
  have currentBorrow : DuplicatePrefixBorrowAuthorization.Positive original.entry.allocation.extra
      (TypedRetagGeneric.protectedGlobal reference.tracker.global fresh).protectedTags
      original.source original.selectedRoot original.maximum original.offset 1 := by
    simpa only [←trackerEq] using currentCapability
  obtain ⟨memory,_,_,addresses,_,_,_,_,_⟩ := RawRootInvocation.preservation #[] before
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
      change (RetagEntry.updatedMemory machine.memory reference.id reference.entry output.child.tree).live.find?
        (fun row => row.1 == original.id) = _
      rw [S02SeparateDestinationTransport.other_live machine.memory reference.id original.id
        reference.entry output.child.tree other]
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
    borrow := currentBorrow }
  exact ⟨destination,rfl,rfl,rfl⟩

end
end DuplicatePrefix.S02WildcardSeparateDestinationInput

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02WildcardSeparateDestinationInput.destination_input_after_argument) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
