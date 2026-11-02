import duplicate_prefix.S02SameDestinationConcreteAllCountResult
import duplicate_prefix.S02SeparateDestinationAllCountResult

namespace DuplicatePrefix.S02ConcreteSourceConcreteReturnAllCountResult
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
noncomputable section

/-- Every count executes and returns without UB for a positive concrete source
and a concrete destination satisfying the current call contract. -/
theorem result
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len count place := by
  by_cases sameAllocation : id = input.contract.destination.id
  · exact S02SameDestinationConcreteAllCountResult.result id tag address len count input nonempty
      sameAllocation returnTag returnConcrete
  · exact S02SeparateDestinationAllCountResult.result id tag address len count input nonempty
      sameAllocation returnTag returnConcrete

end
end DuplicatePrefix.S02ConcreteSourceConcreteReturnAllCountResult

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02ConcreteSourceConcreteReturnAllCountResult.result) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete-source concrete-return all-count dependency {dependency}"
