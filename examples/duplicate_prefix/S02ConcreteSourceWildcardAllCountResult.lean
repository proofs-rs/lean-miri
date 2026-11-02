import duplicate_prefix.S02ConcreteSourceWildcardZeroResult
import duplicate_prefix.S02ConcreteSourceWildcardAcceptedResult
import duplicate_prefix.S02ConcreteSourceWildcardRejectedResult

namespace DuplicatePrefix.S02ConcreteSourceWildcardAllCountResult
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
noncomputable section

/-- Every count returns without UB for the existing positive concrete-source,
distinct wildcard-return contract, including zero, accepted and rejected counts. -/
theorem result
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (different : id ≠ input.contract.destination.id)
    (returnWildcard : input.contract.destination.pointer.provenance = .wildcard) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len count place := by
  by_cases zero : count = 0
  · subst count
    exact S02ConcreteSourceWildcardZeroResult.result id tag address len input nonempty
      different returnWildcard
  by_cases within : count ≤ len/2
  · have positive : 0 < count.toNat := Nat.pos_of_ne_zero (by
      intro h
      apply zero
      exact UInt64.toNat_inj.mp (by simpa using h))
    exact S02ConcreteSourceWildcardAcceptedResult.result id tag address len count input
      nonempty different returnWildcard positive within
  · have rejected : count > len/2 := by
      apply UInt64.lt_iff_toNat_lt.mpr
      have hnot : ¬ count.toNat ≤ (len/2).toNat := by
        intro h
        exact within (UInt64.le_iff_toNat_le.mpr h)
      omega
    exact S02ConcreteSourceWildcardRejectedResult.result id tag address len count input
      nonempty different returnWildcard rejected

end
end DuplicatePrefix.S02ConcreteSourceWildcardAllCountResult

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02ConcreteSourceWildcardAllCountResult.result) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete-source wildcard all-count Result dependency {dependency}"
