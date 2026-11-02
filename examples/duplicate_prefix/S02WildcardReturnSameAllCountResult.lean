import duplicate_prefix.S02WildcardReturnSameZeroResult
import duplicate_prefix.S02ConcreteSourceWildcardSameAcceptedResult
import duplicate_prefix.S02ConcreteSourceWildcardSameRejectedResult
namespace DuplicatePrefix.S02WildcardReturnSameAllCountResult
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification
set_option autoImplicit false
noncomputable section

/-- Every count executes the original call and Return under the unchanged
contract, for a positive concrete source and same-allocation wildcard return. -/
theorem result
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before} {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0)
    (returnWildcard : input.contract.destination.pointer.provenance = .wildcard)
    (sameAllocation : id = input.contract.destination.id) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len count place := by
  by_cases zero : count = 0
  · subst count
    exact S02WildcardReturnSameZeroResult.result id tag address len input nonempty sameAllocation returnWildcard
  by_cases within : count ≤ len/2
  · have positive : (0 : UInt64) < count := by
      apply UInt64.lt_iff_toNat_lt.mpr
      apply Nat.pos_of_ne_zero
      intro h
      apply zero
      exact UInt64.toNat_inj.mp (by simpa using h)
    exact S02ConcreteSourceWildcardSameAcceptedResult.result id tag address len count input nonempty sameAllocation returnWildcard positive within
  · have rejected : count > len/2 := by
      apply UInt64.lt_iff_toNat_lt.mpr
      have hnot : ¬ count.toNat ≤ (len/2).toNat := fun h => within (UInt64.le_iff_toNat_le.mpr h)
      omega
    exact S02ConcreteSourceWildcardSameRejectedResult.result id tag address len count input nonempty sameAllocation returnWildcard rejected
end
end DuplicatePrefix.S02WildcardReturnSameAllCountResult
#print axioms DuplicatePrefix.S02WildcardReturnSameAllCountResult.result
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.S02WildcardReturnSameAllCountResult.result) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved wildcard same all-count dependency {dependency}"
