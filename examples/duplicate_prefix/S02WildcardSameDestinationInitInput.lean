import duplicate_prefix.S02WildcardArgumentScope
import duplicate_prefix.S02SeparateDestinationAuthorization

namespace DuplicatePrefix.S02WildcardSameDestinationInitInput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Physical address separation in the existing contract gives disjoint
same-allocation byte windows for the actual wildcard source witness. -/
theorem disjoint
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance} (address len : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0)
    (reference : DuplicatePrefixReferenceInput.Positive before (Pointer.new .wildcard (Size.ofBytes address)) len)
    (same : reference.id = input.contract.destination.id) :
    reference.offset.toNat+len.toNat ≤ input.contract.destination.offset.toNat ∨
      input.contract.destination.offset.toNat+1 ≤ reference.offset.toNat := by
  have bases := Option.some.inj (reference.cachedBase.symm.trans
    (same ▸ input.contract.destination.cachedBase))
  have baseEq : reference.base = input.contract.destination.base :=
    congrArg AllocAddresses.BaseAddressEntry.address bases
  have sourceFits : reference.base.toNat+reference.offset.toNat < 2^64 := by
    have bounds := reference.storage.bounds
    have fits := reference.addressFits
    omega
  have sourceAddress : address.toNat = reference.base.toNat+reference.offset.toNat := by
    calc
      address.toNat = (reference.base+reference.offset).toNat := congrArg UInt64.toNat reference.pointerAddress
      _ = _ := by rw [UInt64.toNat_add,Nat.mod_eq_of_lt sourceFits]
  have targetAddress := input.contract.destination.address_interval.1
  rcases input.contract.separated with zero | left | right
  · exact False.elim (nonempty zero)
  · change address.toNat+len.toNat ≤ input.contract.destination.pointer.offset.bytes.toNat at left
    rw [sourceAddress,targetAddress,baseEq] at left
    exact Or.inl (by omega)
  · change input.contract.destination.pointer.offset.bytes.toNat+1 ≤ address.toNat at right
    rw [sourceAddress,targetAddress,baseEq] at right
    exact Or.inr (by omega)

/-- Physical reconstruction on the exact wildcard argument machine. The old
concrete destination's authority and tag lookup are transported separately
through the actual wildcard Read and root insertion. -/
def at_current
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance} {address len : UInt64}
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (reference : DuplicatePrefixReferenceInput.Positive before (Pointer.new .wildcard (Size.ofBytes address)) len)
    (fresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615)
    (same : reference.id = input.contract.destination.id)
    (returnTag : BorTag)
    (concrete : input.contract.destination.pointer.provenance = .concrete input.contract.destination.id returnTag)
    (tree : BorrowTree)
    (capacity : tree.locations.size = reference.entry.allocation.extra.locations.size)
    (mapped : ∀ tag query, reference.entry.allocation.extra.indexOfTag tag = some query → tree.indexOfTag tag = some query)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree
      (TypedRetagGeneric.protectedGlobal reference.tracker.global fresh).protectedTags
      input.contract.destination.source input.contract.destination.selectedRoot input.contract.destination.maximum
      input.contract.destination.offset 1) :
    DuplicatePrefixReturnPlaceInput.Input
      (GeneralBorrowRawWildcardWindowFunctionScope.resultMachine (RawRootInvocation.machine #[] before)
        reference.tracker fresh reference.id reference.entry tree) place := by
  let original := input.contract.destination
  let machine := RawRootInvocation.machine #[] before
  let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine machine reference.tracker fresh reference.id reference.entry tree
  have entryEq : reference.entry = original.entry := by
    have live := reference.live
    rw [same] at live
    exact congrArg Prod.snd (Option.some.inj (live.symm.trans original.live))
  obtain ⟨memory,_tracker,_race,addresses,_types,_backend,_ghost,_validation,_extras⟩ := RawRootInvocation.preservation #[] before
  let nextTracker : MachineHooks.BorrowState :=
    ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global fresh,reference.tracker.retagMode⟩
  refine {
    tracker := nextTracker, enabled := rfl,
    pointer := original.pointer, physicalPointer := original.physicalPointer,
    layout := original.layout, aligned := original.aligned,
    id := original.id,
    entry := {original.entry with allocation := original.entry.allocation.setExtra tree},
    base := original.base, offset := original.offset, capacity := original.capacity,
    live := ?_, cachedBase := ?_, pointerAddress := original.pointerAddress,
    nonnull := original.nonnull, addressFits := original.addressFits, bounds := original.bounds,
    size := original.size, bytes := original.bytes, mutable := original.mutable,
    maskValid := original.maskValid, maskLength := original.maskLength, provenanceMap := original.provenanceMap,
    borrowSize := ?_, source := original.source, selectedRoot := original.selectedRoot, maximum := original.maximum,
    binding := ?_, borrow := positive }
  · change (RetagEntry.updatedMemory machine.memory reference.id reference.entry tree).live.find?
      (fun row => row.1 == original.id) = _
    rw [←same,←entryEq]
    exact MemoryCopyBridge.live_lookup_replaced _ _ _
  · change machine.user.addresses.baseAddr.find? (fun row => row.allocId == original.id) = _
    rw [addresses];exact original.cachedBase
  · change tree.locations.size.bytes = original.capacity
    rw [capacity,entryEq];exact original.borrowSize
  · change DuplicatePrefixReferenceInput.Binding machine.user.addresses original.pointer original.id
      original.base (original.entry.allocation.setExtra tree).byteSize tree original.source
    have binding := original.binding
    have concreteOriginal : original.pointer.provenance = .concrete original.id returnTag := concrete
    simp only [DuplicatePrefixReferenceInput.Binding,concreteOriginal] at binding ⊢
    obtain ⟨idEq,parent,sourceEq,tagged⟩ := binding
    exact ⟨idEq,parent,sourceEq,mapped returnTag parent (by rw [entryEq];exact tagged)⟩

end
end DuplicatePrefix.S02WildcardSameDestinationInitInput

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.S02WildcardSameDestinationInitInput.at_current,
      ``DuplicatePrefix.S02WildcardSameDestinationInitInput.disjoint] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved wildcard same init input dependency {dependency}"
