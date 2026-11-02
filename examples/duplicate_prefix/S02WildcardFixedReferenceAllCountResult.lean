import duplicate_prefix.S02WildcardSeparateConcreteAllCountResult
import duplicate_prefix.S02WildcardPositiveIdUnique

namespace DuplicatePrefix.S02WildcardFixedReferenceAllCountResult
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification
set_option autoImplicit false
noncomputable section

/-- The original contract's positive wildcard reference is independent of count.
If its resolved allocation differs from the concrete return place, every count
executes and returns with NoUB. -/
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
      ∀ count : UInt64,
        DuplicatePrefixArgumentCallResult.Result options limits remaining span before
          (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len count place := by
  cases input.contract.reference with
  | empty zero _ => exact False.elim (nonempty zero)
  | positive pointer encoding reference =>
    have pointerEq := DuplicatePrefixSliceArgument.Argument.pointer.inj encoding
    subst pointer
    refine ⟨reference,?_⟩
    intro different count
    obtain ⟨resolved,run⟩ := S02WildcardSeparateConcreteAllCountResult.result
      address len count input nonempty returnTag returnConcrete
    have sameId := S02WildcardPositiveIdUnique.same_id address len reference resolved
    exact run (by rw [←sameId]; exact different)

end
end DuplicatePrefix.S02WildcardFixedReferenceAllCountResult

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardFixedReferenceAllCountResult.result) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard fixed-reference all-count dependency {dependency}"
