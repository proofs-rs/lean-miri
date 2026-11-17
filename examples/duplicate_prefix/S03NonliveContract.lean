import duplicate_prefix.S03NonliveConcreteContract
import duplicate_prefix.S03NonliveWildcardContract

namespace DuplicatePrefix.S03NonliveContract
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
open DuplicatePrefixCallSpecification S05ConsistentCallSpecification
set_option autoImplicit false
noncomputable section

/-- Every count and original return-provenance case for the supported nonlive
concrete empty argument. Metadata/live absence are initial classification
facts; all execution and final-state obligations follow internally. -/
theorem complete {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (argumentId : AllocId) (parentTag : BorTag) (argumentConcrete : pointer.provenance = .concrete argumentId parentTag)
    (argumentMetadata : DuplicatePrefixEmptyReferenceInput.Metadata before.memory argumentId (some parentTag))
    (argumentAbsent : before.memory.live.find? (fun row => row.1 == argumentId) = none)
    (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.pointer pointer) 0 count place := by
  cases provenance : input.contract.destination.pointer.provenance with
  | concrete id tag =>
    have binding := input.contract.destination.binding
    simp only [DuplicatePrefixReferenceInput.Binding,provenance] at binding
    have concrete : input.contract.destination.pointer.provenance = .concrete input.contract.destination.id tag :=
      provenance.trans (congrArg (fun id => Provenance.concrete id tag) binding.1)
    exact S03NonliveConcreteContract.complete input tag concrete argumentId parentTag argumentConcrete argumentMetadata argumentAbsent count
  | wildcard =>
    exact S03NonliveWildcardContract.complete input provenance argumentId parentTag argumentConcrete argumentMetadata argumentAbsent count

end
end DuplicatePrefix.S03NonliveContract
