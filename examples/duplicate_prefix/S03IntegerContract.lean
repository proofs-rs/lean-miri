import duplicate_prefix.S03IntegerConcreteContract
import duplicate_prefix.S03IntegerWildcardContract

namespace DuplicatePrefix.S03IntegerContract
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
open DuplicatePrefixCallSpecification S05ConsistentCallSpecification
set_option autoImplicit false
noncomputable section

/-- Every count and original return-provenance case for the integer/NoProv
empty argument, from the revised initial-data contract to the original actual
call safety result. Other argument-provenance cases are separate obligations. -/
theorem complete {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before} {address : UInt64}
    {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before (.integer address) 0 place)
    (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.integer address) 0 count place := by
  cases provenance : input.contract.destination.pointer.provenance with
  | concrete id tag =>
    have binding := input.contract.destination.binding
    simp only [DuplicatePrefixReferenceInput.Binding,provenance] at binding
    have concrete : input.contract.destination.pointer.provenance = .concrete input.contract.destination.id tag :=
      provenance.trans (congrArg (fun id => Provenance.concrete id tag) binding.1)
    exact S03IntegerConcreteContract.complete input tag concrete count
  | wildcard => exact S03IntegerWildcardContract.complete input provenance count

end
end DuplicatePrefix.S03IntegerContract
