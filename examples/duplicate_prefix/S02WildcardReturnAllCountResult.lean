import duplicate_prefix.S03EmptyContract
import duplicate_prefix.S02WildcardReturnSameAllCountResult
import duplicate_prefix.S02WildcardReturnSameAllCountResultWildcard
import duplicate_prefix.S02ConcreteSourceWildcardAllCountResult
import duplicate_prefix.S02WildcardSourceWildcardFixedReferenceAllCountResult
namespace DuplicatePrefix.S02WildcardReturnAllCountResult
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification
set_option autoImplicit false
noncomputable section

/-- The unchanged contract executes the original call and Return for every
argument, length and count when the return provenance is wildcard. All source
representations and allocation relations are derived internally. -/
theorem result
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {argument : DuplicatePrefixSliceArgument.Argument} {place : MPlaceTy Provenance}
    (len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before argument len place)
    (returnWildcard : input.contract.destination.pointer.provenance = .wildcard) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument len count place := by
  by_cases zero : len = 0
  · subst len
    exact S03EmptyContract.complete input count
  cases input.contract.reference with
  | empty empty _ => exact False.elim (zero empty)
  | positive pointer encoding reference =>
    subst argument
    cases pointer with
    | mk offset provenance =>
      cases offset with
      | mk address =>
        cases provenance with
        | concrete id tag =>
          by_cases same : id = input.contract.destination.id
          · exact S02WildcardReturnSameAllCountResult.result id tag address len count input zero returnWildcard same
          · exact S02ConcreteSourceWildcardAllCountResult.result id tag address len count input zero same returnWildcard
        | wildcard =>
          by_cases same : reference.id = input.contract.destination.id
          · exact S02WildcardReturnSameAllCountResultWildcard.same_id address len count input zero returnWildcard reference same
          · obtain ⟨resolved,run⟩ := S02WildcardSourceWildcardFixedReferenceAllCountResult.result address len input zero returnWildcard
            have unique := S02WildcardPositiveIdUnique.same_id address len reference resolved
            exact run (by rw [←unique];exact same) count
end
end DuplicatePrefix.S02WildcardReturnAllCountResult
#print axioms DuplicatePrefix.S02WildcardReturnAllCountResult.result
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.S02WildcardReturnAllCountResult.result) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved wildcard return all-count dependency {dependency}"
