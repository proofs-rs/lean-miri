import duplicate_prefix.S02SeparateDestinationTransport

namespace DuplicatePrefix.S02SeparateDestinationEntryIdentity
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- The current distinct return input has the same allocation row and
concrete parent as the original call contract. -/
theorem from_contract
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
    (firstFresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615)
    (destination : DuplicatePrefixReturnPlaceInput.Input
      (GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
        reference.tracker firstFresh reference.id reference.entry tag reference.offset len) place)
    (different : id ≠ input.contract.destination.id)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag) :
    id = reference.id ∧ destination.id = input.contract.destination.id ∧
    destination.entry = input.contract.destination.entry ∧
    destination.pointer.provenance = .concrete destination.id returnTag := by
  have idEq : id = reference.id := by
    have binding := reference.binding
    simp only [DuplicatePrefixReferenceInput.Binding,Pointer.new] at binding
    exact binding.1
  have physical := destination.physicalPointer.symm.trans input.contract.destination.physicalPointer
  have provenance := congrArg (fun ptr : Pointer (Option Provenance) => ptr.provenance) physical
  simp only [Pointer.withOptionalProvenance] at provenance
  have same := Option.some.inj provenance
  have concreteOriginal : destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag := same.trans returnConcrete
  have destId : destination.id = input.contract.destination.id := by
    have binding := destination.binding
    simp only [DuplicatePrefixReferenceInput.Binding,concreteOriginal] at binding
    exact binding.1.symm
  let current := GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
    reference.tracker firstFresh reference.id reference.entry tag reference.offset len
  have destEntry : destination.entry = input.contract.destination.entry := by
    have other : reference.id ≠ destination.id := by simpa only [←destId,←idEq] using different
    have live : current.memory.live.find? (fun row => row.1 == destination.id) =
        some (destination.id,input.contract.destination.entry) := by
      change (RetagEntry.updatedMemory (RawRootInvocation.machine #[] before).memory reference.id
        reference.entry (GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
          reference.tracker tag reference.offset len)).live.find? (fun row => row.1 == destination.id) = _
      rw [S02SeparateDestinationTransport.other_live _ _ _ _ _ other]
      have preserved := (RawRootInvocation.preservation #[] before).1
      rw [preserved,destId]
      exact input.contract.destination.live
    exact congrArg Prod.snd (Option.some.inj (destination.live.symm.trans live))
  exact ⟨idEq,destId,destEntry,by rw [destId]; exact concreteOriginal⟩

end DuplicatePrefix.S02SeparateDestinationEntryIdentity

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationEntryIdentity.from_contract) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate destination entry identity dependency {dependency}"
