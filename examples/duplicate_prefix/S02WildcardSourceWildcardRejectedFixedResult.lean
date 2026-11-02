import duplicate_prefix.S02WildcardSourceWildcardRejectedResult
import duplicate_prefix.S02WildcardPositiveIdUnique

namespace DuplicatePrefix.S02WildcardSourceWildcardRejectedFixedResult
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification
set_option autoImplicit false
noncomputable section

/-- Rejected-count NoUB for the wildcard source resolved by the original input contract,
when the wildcard return place resolves to a distinct allocation. -/
theorem result
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0)
    (returnWildcard : input.contract.destination.pointer.provenance = .wildcard)
    (rejected : count > len/2) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new .wildcard (Size.ofBytes address)) len),
      reference.id ≠ input.contract.destination.id →
      DuplicatePrefixArgumentCallResult.Result options limits remaining span before
        (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len count place := by
  cases input.contract.reference with
  | empty zero _ => exact False.elim (nonempty zero)
  | positive pointer encoding reference =>
    have pointerEq := DuplicatePrefixSliceArgument.Argument.pointer.inj encoding
    subst pointer
    refine ⟨reference,?_⟩
    intro different
    obtain ⟨resolved,run⟩ := S02WildcardSourceWildcardRejectedResult.result
      address len count input nonempty returnWildcard rejected
    have sameId := S02WildcardPositiveIdUnique.same_id address len reference resolved
    exact run (by rw [←sameId]; exact different)

end
end DuplicatePrefix.S02WildcardSourceWildcardRejectedFixedResult

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardSourceWildcardRejectedFixedResult.result) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard/wildcard rejected fixed-result dependency {dependency}"
