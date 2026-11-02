import duplicate_prefix.S02ConcreteSourceConcreteReturnAllCountResult
import duplicate_prefix.S02WildcardSourceConcreteReturnAllCountResult
import duplicate_prefix.S03EmptyContract

namespace DuplicatePrefix.S02ConcreteReturnAllCountResult
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
open DuplicatePrefixCallSpecification
set_option autoImplicit false
noncomputable section

/-- Positive pointer sources exhaust concrete/wildcard provenance. No allocation
relation or positive-reference witness is supplied by the caller. -/
theorem positive_result
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (pointer : Pointer Provenance) (len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer pointer) len place)
    (nonempty : len ≠ 0) (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer pointer) len count place := by
  rcases pointer with ⟨⟨address⟩,provenance⟩
  cases provenance with
  | concrete id tag =>
    exact S02ConcreteSourceConcreteReturnAllCountResult.result id tag address len count
      input nonempty returnTag returnConcrete
  | wildcard =>
    exact S02WildcardSourceConcreteReturnAllCountResult.result address len count
      input nonempty returnTag returnConcrete

/-- All lengths and counts for a concrete return destination in the current
explicit call domain. Empty arguments include integer/no-provenance encodings;
positive arguments are pointers by the domain's Reference constructor. This
case elimination establishes no ordinary-input coverage beyond that domain. -/
theorem result
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {argument : DuplicatePrefixSliceArgument.Argument} {place : MPlaceTy Provenance}
    (len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      argument len place)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument len count place := by
  by_cases zero : len = 0
  · subst len
    exact S03EmptyContract.complete input count
  · cases input.contract.reference with
    | empty emptyLength _ => exact False.elim (zero emptyLength)
    | positive pointer encoding _ =>
      subst argument
      exact positive_result pointer len count input zero returnTag returnConcrete

end
end DuplicatePrefix.S02ConcreteReturnAllCountResult

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S02ConcreteReturnAllCountResult." then
      for dependency in (←collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved concrete return facade dependency {dependency}"
