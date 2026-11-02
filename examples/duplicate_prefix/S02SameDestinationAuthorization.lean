import duplicate_prefix.S02SameDestinationInput
import duplicate_prefix.S02ConcreteArgumentScope

namespace DuplicatePrefix.S02SameDestinationAuthorization
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Actual typed arguments and a derived general return-place Input share one
exact same-allocation current machine. The destination entry is the real
source FnEntry tree replacement, with full post-constructor authorization. -/
theorem destination_input_after_argument
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
        destination.entry = {reference.entry with allocation := reference.entry.allocation.setExtra (GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra reference.tracker tag reference.offset len)} ∧
        destination.offset = input.contract.destination.offset := by
  obtain ⟨reference,fresh,actual⟩ := S02ConcreteArgumentScope.argument_body id tag address len count input nonempty
  obtain ⟨destination,destId,destEntry,destOffset,_source,_selected,_maximum⟩ :=
    S02SameDestinationInput.at_actual_current id tag address len input nonempty same reference fresh
  have binding := reference.binding
  simp only [DuplicatePrefixReferenceInput.Binding,Pointer.new] at binding
  have destId' : reference.id = input.contract.destination.id := binding.1.symm.trans same
  have entryEq : reference.entry = input.contract.destination.entry := by
    have live := reference.live
    rw [destId'] at live
    exact congrArg Prod.snd (Option.some.inj (live.symm.trans input.contract.destination.live))
  rw [←entryEq] at destEntry
  exact ⟨reference,fresh,actual,destination,destId,destEntry,destOffset⟩

end
end DuplicatePrefix.S02SameDestinationAuthorization

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02SameDestinationAuthorization.destination_input_after_argument) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
