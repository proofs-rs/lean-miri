import duplicate_prefix.S02WildcardZeroResult
import duplicate_prefix.S02WildcardAcceptedResult
import duplicate_prefix.S02WildcardRejectedResult

namespace DuplicatePrefix.S02WildcardSeparateConcreteAllCountResult
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
noncomputable section

/-- For every count, the actual positive wildcard slice call returns without UB
when its resolved source allocation is distinct from the concrete return place. -/
theorem result
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (address len count : UInt64)
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
        (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len count place := by
  by_cases zero : count = 0
  · subst count
    exact S02WildcardZeroResult.result address len input nonempty returnTag returnConcrete
  by_cases within : count ≤ len/2
  · have positive : 0 < count.toNat := Nat.pos_of_ne_zero (by
      intro h
      apply zero
      exact UInt64.toNat_inj.mp (by simpa using h))
    exact S02WildcardAcceptedResult.result address len count input nonempty positive within
      returnTag returnConcrete
  · have rejected : count > len/2 := by
      apply UInt64.lt_iff_toNat_lt.mpr
      have hnot : ¬ count.toNat ≤ (len/2).toNat := by
        intro h
        exact within (UInt64.le_iff_toNat_le.mpr h)
      omega
    exact S02WildcardRejectedResult.result address len count input nonempty returnTag
      returnConcrete rejected

end
end DuplicatePrefix.S02WildcardSeparateConcreteAllCountResult

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardSeparateConcreteAllCountResult.result) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard separate concrete all-count dependency {dependency}"
