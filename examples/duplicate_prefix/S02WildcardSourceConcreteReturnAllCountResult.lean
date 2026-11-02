import duplicate_prefix.S02WildcardSameDestinationAllCountResult
import duplicate_prefix.S02WildcardFixedReferenceAllCountResult
namespace DuplicatePrefix.S02WildcardSourceConcreteReturnAllCountResult
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification
set_option autoImplicit false
noncomputable section

/-- Positive wildcard source and concrete return destination execute the original
call and Return for every count, at either allocation relation. The original
positive witness is extracted from the contract, not supplied by the caller. -/
theorem result
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before} {place : MPlaceTy Provenance}
    (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance = .concrete input.contract.destination.id returnTag) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len count place := by
  cases input.contract.reference with
  | empty zero _ => exact False.elim (nonempty zero)
  | positive pointer encoding reference =>
    have pointerEq := DuplicatePrefixSliceArgument.Argument.pointer.inj encoding
    subst pointer
    by_cases same : reference.id = input.contract.destination.id
    · exact S02WildcardSameDestinationAllCountResult.same_id address len count input nonempty returnTag returnConcrete reference same
    · obtain ⟨resolved,run⟩ := S02WildcardFixedReferenceAllCountResult.result address len input nonempty returnTag returnConcrete
      have unique := S02WildcardPositiveIdUnique.same_id address len reference resolved
      exact run (by rw [←unique];exact same) count
end
end DuplicatePrefix.S02WildcardSourceConcreteReturnAllCountResult
#print axioms DuplicatePrefix.S02WildcardSourceConcreteReturnAllCountResult.result
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.S02WildcardSourceConcreteReturnAllCountResult.result) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved wildcard source concrete return all-count dependency {dependency}"
