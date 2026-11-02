import duplicate_prefix.S02ConcreteArgumentScope

namespace DuplicatePrefix.S02SeparateDestinationTransport
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Replacing the argument allocation during real FnEntry leaves a distinct
destination allocation's live row untouched. -/
theorem other_live {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (source destination : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K) (tree : BorrowTree)
    (different : source ≠ destination) :
    (RetagEntry.updatedMemory memory source entry tree).live.find?
      (fun row => row.1 == destination) =
      memory.live.find? (fun row => row.1 == destination) := by
  have predicate :
      (fun row : AllocId × LocalAllocation Provenance BorrowTree K =>
        (row.1 != source) && (row.1 == destination)) =
      (fun row => row.1 == destination) := by
    funext row
    by_cases same : row.1 = destination
    · simp [same,Ne.symm different]
    · simp [same]
  simp only [RetagEntry.updatedMemory,Array.find?_push]
  simp only [show (source == destination) = false from by simp [different],
    Bool.false_eq_true,↓reduceIte,Option.or_none,Array.find?_filter]
  exact congrArg (fun test => memory.live.find? test) predicate

/-- The actual positive concrete argument pass changes only its own live
allocation row. In the separate-allocation case the original destination's
live row, address cache and required metadata remain available on the exact
post-argument machine. Borrow authorization under the updated global
protector set is a further obligation. -/
theorem destination_data_after_argument
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
        some (input.contract.destination.id,input.contract.destination.entry) ∧
      current.user.addresses.baseAddr.find? (fun row => row.allocId == input.contract.destination.id) =
        some ⟨input.contract.destination.id,input.contract.destination.base⟩ ∧
      current.user.payload.payload.user.runtime.extras.allocations.find?
        (fun row => row.1 == input.contract.destination.id) =
        some (input.contract.destination.id,⟨none,#[]⟩) := by
  obtain ⟨reference,fresh,actual⟩ := S02ConcreteArgumentScope.argument_body
    id tag address len count input nonempty
  have idEq : id = reference.id := by
    have binding := reference.binding
    simp only [DuplicatePrefixReferenceInput.Binding,Pointer.new] at binding
    exact binding.1
  have other : reference.id ≠ input.contract.destination.id := idEq ▸ different
  let machine := RawRootInvocation.machine #[] before
  have initial := RawRootInvocation.preservation #[] before
  obtain ⟨live,_,_,addresses,_,_,_,_,extras⟩ := initial
  refine ⟨reference,fresh,actual,?_,?_,?_⟩
  · change (RetagEntry.updatedMemory machine.memory reference.id reference.entry
      (GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra reference.tracker
        tag reference.offset len)).live.find? (fun row => row.1 == input.contract.destination.id) = _
    rw [other_live machine.memory reference.id input.contract.destination.id reference.entry _ other]
    rw [live]
    exact input.contract.destination.live
  · change machine.user.addresses.baseAddr.find? (fun row => row.allocId == input.contract.destination.id) = _
    rw [addresses]
    exact input.contract.destination.cachedBase
  · change machine.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == input.contract.destination.id) = _
    rw [extras]
    exact input.return_extras

end
end DuplicatePrefix.S02SeparateDestinationTransport

open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S02SeparateDestinationTransport.other_live,
      ``DuplicatePrefix.S02SeparateDestinationTransport.destination_data_after_argument] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
