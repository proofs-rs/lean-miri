import duplicate_prefix.S02WildcardSeparateDestinationCall
import duplicate_prefix.S02WildcardSeparateDestinationWildcardCall

namespace DuplicatePrefix.S02WildcardSeparateDestinationAllReturns
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- A positive wildcard argument enters the actual root call for either
provenance of a distinct return allocation. The only case guard is whether
the derived source allocation equals the destination allocation. -/
theorem call_entry_if_distinct
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) :
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
  cases provenance : input.contract.destination.pointer.provenance with
  | wildcard =>
      exact S02WildcardSeparateDestinationWildcardCall.wildcard_return_call_entry
        address len count input nonempty provenance
  | concrete id tag =>
      have binding := input.contract.destination.binding
      simp only [DuplicatePrefixReferenceInput.Binding,provenance] at binding
      have sameId : id = input.contract.destination.id := binding.1
      subst id
      exact S02WildcardSeparateDestinationCall.concrete_return_call_entry
        address len count input nonempty tag provenance

end
end DuplicatePrefix.S02WildcardSeparateDestinationAllReturns

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms
      ``DuplicatePrefix.S02WildcardSeparateDestinationAllReturns.call_entry_if_distinct) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
