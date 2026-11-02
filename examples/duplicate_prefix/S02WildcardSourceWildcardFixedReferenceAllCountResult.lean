import duplicate_prefix.S02WildcardSourceWildcardZeroResult
import duplicate_prefix.S02WildcardSourceWildcardRejectedResult
import duplicate_prefix.S02WildcardSourceWildcardAcceptedResult
import duplicate_prefix.S02WildcardPositiveIdUnique

namespace DuplicatePrefix.S02WildcardSourceWildcardFixedReferenceAllCountResult
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification
set_option autoImplicit false
noncomputable section

/-- The original contract resolves one positive wildcard source independently of
count. If that source allocation differs from the wildcard return allocation,
every count completes the original call with NoUB. -/
theorem result
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (address len : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0)
    (returnWildcard : input.contract.destination.pointer.provenance = .wildcard) :
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
    by_cases zero : count = 0
    · subst count
      obtain ⟨resolved,run⟩ := S02WildcardSourceWildcardZeroResult.result
        address len input nonempty returnWildcard
      have sameId := S02WildcardPositiveIdUnique.same_id address len reference resolved
      exact run (by rw [←sameId]; exact different)
    by_cases within : count ≤ len/2
    · have positive : 0 < count.toNat := Nat.pos_of_ne_zero (by
        intro h
        apply zero
        exact UInt64.toNat_inj.mp (by simpa using h))
      obtain ⟨resolved,run⟩ := S02WildcardSourceWildcardAcceptedResult.result
        address len count input nonempty returnWildcard positive within
      have sameId := S02WildcardPositiveIdUnique.same_id address len reference resolved
      exact run (by rw [←sameId]; exact different)
    · have rejected : count > len/2 := by
        apply UInt64.lt_iff_toNat_lt.mpr
        have hnot : ¬ count.toNat ≤ (len/2).toNat := by
          intro h
          exact within (UInt64.le_iff_toNat_le.mpr h)
        omega
      obtain ⟨resolved,run⟩ := S02WildcardSourceWildcardRejectedResult.result
        address len count input nonempty returnWildcard rejected
      have sameId := S02WildcardPositiveIdUnique.same_id address len reference resolved
      exact run (by rw [←sameId]; exact different)

end
end DuplicatePrefix.S02WildcardSourceWildcardFixedReferenceAllCountResult

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardSourceWildcardFixedReferenceAllCountResult.result) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard/wildcard fixed-reference all-count dependency {dependency}"
