import duplicate_prefix.S02WildcardBaseArgumentScope
import duplicate_prefix.S02WildcardInteriorArgumentScope

namespace DuplicatePrefix.S02WildcardArgumentScope
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Every positive wildcard pointer in the current call contract executes
both real typed FnEntry argument passes on the original raw call frame. The
same theorem covers exact inverse-map bases and interior hits, arbitrary
multiple roots and coherent free pools. No retag success is assumed. -/
theorem argument_body
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
      let root := RawRootInvocation.root before place input.contract.model.noDataRace
      let machine := RawRootInvocation.machine #[] before
      let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine machine reference.tracker fresh
        reference.id reference.entry output.child.tree
      let cfg := PreparedContracts.actualConfig options () (remaining+1) span
      let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
          (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
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
              reference.id reference.tracker.global.nextPointerTag) count).frame current) := by
  cases input.contract.reference with
  | empty zero _ => exact False.elim (nonempty zero)
  | positive pointer encoding reference =>
    have pointerEq := DuplicatePrefixSliceArgument.Argument.pointer.inj encoding
    subst pointer
    obtain ⟨_,geometry⟩ := S02WildcardArgumentGeometry.cases address len reference
    rcases geometry with ⟨same,_,position,valid,ordered,row⟩ | ⟨position,cut,row,inside⟩
    · obtain ⟨output,fresh,run,actual⟩ := S02WildcardBaseArgumentScope.argument_body
        address len count input reference same position valid ordered row
      refine ⟨reference,output,fresh,run,?_⟩
      simpa only [GeneralBorrowRawWildcardFunctionScope.resultMachine,
        GeneralBorrowRawWildcardWindowFunctionScope.resultMachine] using actual
    · obtain ⟨output,fresh,run,actual⟩ := S02WildcardInteriorArgumentScope.argument_body
        address len count input reference position cut row inside
      exact ⟨reference,output,fresh,run,actual⟩

end
end DuplicatePrefix.S02WildcardArgumentScope

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02WildcardArgumentScope.argument_body) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
