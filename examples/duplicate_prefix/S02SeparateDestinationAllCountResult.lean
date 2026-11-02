import duplicate_prefix.S02SeparateDestinationZeroResult
import duplicate_prefix.S02AcceptedActualReturnResult
import duplicate_prefix.S02SeparateDestinationRejectedReturn

namespace DuplicatePrefix.S02SeparateDestinationAllCountResult
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
noncomputable section

/-- Every count executes and returns without UB for a positive concrete source
and a distinct concrete destination satisfying the current call contract. -/
theorem result
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (different : id ≠ input.contract.destination.id)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len count place := by
  by_cases zero : count = 0
  · subst count
    exact S02SeparateDestinationZeroResult.result id tag address len input nonempty different
      returnTag returnConcrete
  by_cases within : count ≤ len/2
  · have positive : 0 < count.toNat := Nat.pos_of_ne_zero (by
      intro h
      apply zero
      exact UInt64.toNat_inj.mp (by simpa using h))
    exact S02AcceptedActualReturnResult.result id tag address len count input nonempty different
      returnTag returnConcrete positive within
  · have rejected : count > len/2 := by
      apply UInt64.lt_iff_toNat_lt.mpr
      have hnot : ¬ count.toNat ≤ (len/2).toNat := by
        intro h
        exact within (UInt64.le_iff_toNat_le.mpr h)
      omega
    exact S02SeparateDestinationRejectedReturn.result id tag address len count input nonempty different
      returnTag returnConcrete rejected

end
end DuplicatePrefix.S02SeparateDestinationAllCountResult

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationAllCountResult.result) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate-destination all-count dependency {dependency}"
