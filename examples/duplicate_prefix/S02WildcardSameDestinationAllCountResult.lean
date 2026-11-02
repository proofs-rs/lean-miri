import duplicate_prefix.S02WildcardSameDestinationZeroResult
import duplicate_prefix.S02WildcardSameDestinationAcceptedResult
import duplicate_prefix.S02WildcardSameDestinationRejectedResult
namespace DuplicatePrefix.S02WildcardSameDestinationAllCountResult
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification
set_option autoImplicit false
noncomputable section

/-- Every count executes the original call and Return under the unchanged
contract, fixing the original positive wildcard witness and same-allocation case. -/
theorem same_id
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before} {place : MPlaceTy Provenance}
    (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance = .concrete input.contract.destination.id returnTag)
    (reference : DuplicatePrefixReferenceInput.Positive before (Pointer.new .wildcard (Size.ofBytes address)) len)
    (same : reference.id = input.contract.destination.id) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len count place := by
  by_cases zero : count = 0
  · subst count
    exact S02WildcardSameDestinationZeroResult.same_id address len input nonempty returnTag returnConcrete reference same
  by_cases within : count ≤ len/2
  · have positive : (0 : UInt64) < count := by
      apply UInt64.lt_iff_toNat_lt.mpr
      apply Nat.pos_of_ne_zero
      intro h
      apply zero
      exact UInt64.toNat_inj.mp (by simpa using h)
    exact S02WildcardSameDestinationAcceptedResult.same_id address len count input nonempty returnTag returnConcrete positive within reference same
  · have rejected : count > len/2 := by
      apply UInt64.lt_iff_toNat_lt.mpr
      have hnot : ¬ count.toNat ≤ (len/2).toNat := fun h => within (UInt64.le_iff_toNat_le.mpr h)
      omega
    exact S02WildcardSameDestinationRejectedResult.same_id address len count input nonempty returnTag returnConcrete rejected reference same
end
end DuplicatePrefix.S02WildcardSameDestinationAllCountResult
#print axioms DuplicatePrefix.S02WildcardSameDestinationAllCountResult.same_id
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.S02WildcardSameDestinationAllCountResult.same_id) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved wildcard same all-count dependency {dependency}"
