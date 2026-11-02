import duplicate_prefix.S02ConcreteArgumentScope
import duplicate_prefix.S02PositiveInitBridge

namespace DuplicatePrefix.S02SameDestinationLiveTransport
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- The reference used by the real positive argument pass has a source window
disjoint from the destination byte, even when both share a live allocation. -/
theorem actual_reference_disjoint
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (same : id = input.contract.destination.id)
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new (.concrete id tag) (Size.ofBytes address)) len) :
    reference.offset.toNat + len.toNat ≤ input.contract.destination.offset.toNat ∨
      input.contract.destination.offset.toNat + 1 ≤ reference.offset.toNat := by
  have binding := reference.binding
  simp only [DuplicatePrefixReferenceInput.Binding,Pointer.new] at binding
  have idEq : id = reference.id := binding.1
  have destId : reference.id = input.contract.destination.id := idEq.symm.trans same
  have bases := Option.some.inj (reference.cachedBase.symm.trans
    (destId ▸ input.contract.destination.cachedBase))
  have baseEq : reference.base = input.contract.destination.base :=
    congrArg Miri.Memory.AllocAddresses.BaseAddressEntry.address bases
  have sourceFits : reference.base.toNat + reference.offset.toNat < 2^64 := by
    have bounds := reference.storage.bounds
    have fits := reference.addressFits
    omega
  have sourceAddress : address.toNat = reference.base.toNat + reference.offset.toNat := by
    calc
      address.toNat = (reference.base+reference.offset).toNat :=
        congrArg UInt64.toNat reference.pointerAddress
      _ = _ := by rw [UInt64.toNat_add,Nat.mod_eq_of_lt sourceFits]
  have targetAddress := input.contract.destination.address_interval.1
  rcases input.contract.separated with zero | left | right
  · exact False.elim (nonempty zero)
  · change address.toNat + len.toNat ≤ input.contract.destination.pointer.offset.bytes.toNat at left
    rw [sourceAddress,targetAddress,baseEq] at left
    exact Or.inl (by omega)
  · change input.contract.destination.pointer.offset.bytes.toNat + 1 ≤ address.toNat at right
    rw [sourceAddress,targetAddress,baseEq] at right
    exact Or.inr (by omega)

/-- Exact live-row transport when the argument and destination share an allocation.
The real positive argument body executes, and the destination's original
allocation record is replaced by the tree produced by the actual FnEntry
Read and child constructor. This does not yet assert authorization at the
disjoint destination byte in that new tree. -/
theorem destination_live_after_argument
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (same : id = input.contract.destination.id) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
      (fresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615),
      let root := RawRootInvocation.root before place input.contract.model.noDataRace
      let machine := RawRootInvocation.machine #[] before
      let current := GeneralBorrowRawFnEntryScope.resultMachine machine reference.tracker fresh
        reference.id reference.entry tag reference.offset len
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
      current.memory.live.find? (fun row => row.1 == input.contract.destination.id) =
        some (input.contract.destination.id,
          {(input.contract.destination.entry) with allocation :=
            (input.contract.destination.entry.allocation.setExtra
              (GeneralBorrowRawFnEntryArgument.finalTree
                input.contract.destination.entry.allocation.extra reference.tracker
                tag reference.offset len))}) := by
  obtain ⟨reference,fresh,actual⟩ := S02ConcreteArgumentScope.argument_body
    id tag address len count input nonempty
  have idEq : id = reference.id := by
    have binding := reference.binding
    simp only [DuplicatePrefixReferenceInput.Binding,Pointer.new] at binding
    exact binding.1
  have destId : reference.id = input.contract.destination.id := idEq.symm.trans same
  have entryEq : reference.entry = input.contract.destination.entry := by
    have live := reference.live
    rw [destId] at live
    exact congrArg Prod.snd (Option.some.inj (live.symm.trans input.contract.destination.live))
  let machine := RawRootInvocation.machine #[] before
  refine ⟨reference,fresh,actual,?_⟩
  change (RetagEntry.updatedMemory machine.memory reference.id reference.entry
    (GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra reference.tracker
      tag reference.offset len)).live.find? (fun row => row.1 == input.contract.destination.id) = _
  rw [← destId,← entryEq]
  exact MemoryCopyBridge.live_lookup_replaced machine.memory reference.id _

end
end DuplicatePrefix.S02SameDestinationLiveTransport

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02SameDestinationLiveTransport.destination_live_after_argument) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
  for ax in (← collectAxioms ``DuplicatePrefix.S02SameDestinationLiveTransport.actual_reference_disjoint) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
