import duplicate_prefix.S02WildcardSeparateDestinationTail
import duplicate_prefix.S02WildcardCallPreamble

namespace DuplicatePrefix.S02WildcardSeparateDestinationCall
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The actual root call is initialized for a positive wildcard source whose
resolved allocation differs from the concrete return allocation. The
allocation inequality is a case guard on the resolved input, not an assumed
success of an interpreter operation. -/
theorem concrete_return_call_entry
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new .wildcard (Size.ofBytes address)) len),
      reference.id ≠ input.contract.destination.id →
        ∃ final,
          Call.initStackFrame
            (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
            RootBody.reflected.functionInstance RootBody.reflected.body
            RootCompilerFacts.rootAbi
            #[.Copy (DuplicatePrefixSliceArgument.first
              (config options remaining span).access.runtime.base
              (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len),
              .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
              ⟨⟨#[]⟩,before⟩ = .ok () final := by
  obtain ⟨reference,output,fresh,tailReady⟩ :=
    S02WildcardSeparateDestinationTail.concrete_after_argument
      address len count input nonempty returnTag returnConcrete
  refine ⟨reference,?_⟩
  intro different
  obtain ⟨final,argument,tail⟩ := tailReady different
  obtain ⟨after,preambleArg,preambleContinue⟩ :=
    S02WildcardCallPreamble.prefix_and_continuation address len count input nonempty
  let machine := RawRootInvocation.machine #[] before
  let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine machine reference.tracker fresh
    reference.id reference.entry output.child.tree
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
  let frame := (RootArgumentsTwo.result
    (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
      reference.id reference.tracker.global.nextPointerTag) count).frame
  have sameAfter : after = Storage.withCurrent #[] frame current := by
    have resultEq := preambleArg.symm.trans argument
    exact (EStateM.Result.ok.inj resultEq).2
  exact ⟨final,preambleContinue final (sameAfter ▸ tail)⟩

end
end DuplicatePrefix.S02WildcardSeparateDestinationCall

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms
      ``DuplicatePrefix.S02WildcardSeparateDestinationCall.concrete_return_call_entry) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
