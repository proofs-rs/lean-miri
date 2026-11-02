import duplicate_prefix.S02WildcardZeroBody
import duplicate_prefix.SuccessfulTraceTerminal
import duplicate_prefix.DuplicatePrefixArgumentCallResult

namespace DuplicatePrefix.S02WildcardZeroResult
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Full actual-call Result, including progress from every finite trace prefix,
for count-zero positive wildcard input with resolved distinct concrete return. -/
theorem result
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (address len : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new .wildcard (Size.ofBytes address)) len),
      reference.id ≠ input.contract.destination.id →
        DuplicatePrefixArgumentCallResult.Result options limits remaining span before
          (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len 0 place := by
  obtain ⟨reference,ready⟩ :=
    S02WildcardZeroBody.executes address len input nonempty returnTag returnConcrete
  refine ⟨reference,?_⟩
  intro different
  obtain ⟨installed,done,actual,trace,terminal,empty,noErrors,noUB⟩ := ready different
  exact ⟨installed,done,actual,trace,terminal,empty,noErrors,noUB,
    SuccessfulTraceTerminal.prefix_step_success trace terminal⟩

end
end DuplicatePrefix.S02WildcardZeroResult

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardZeroResult.result) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard zero-result dependency {dependency}"
