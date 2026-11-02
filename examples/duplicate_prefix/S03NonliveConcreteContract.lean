import duplicate_prefix.S03NonliveZeroContract
import duplicate_prefix.S03NonlivePositiveContract

namespace DuplicatePrefix.S03NonliveConcreteContract
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
open DuplicatePrefixCallSpecification S05ConsistentCallSpecification
set_option autoImplicit false
noncomputable section

/-- Every count for the supported nonlive concrete empty argument case and a
general concrete return destination. Raw initial metadata/live absence select
this branch; all execution, numeric and final borrow facts are derived from
the existing consistent contract. Other reference families remain separate. -/
theorem complete {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (tag : BorTag) (concrete : input.contract.destination.pointer.provenance = .concrete input.contract.destination.id tag)
    (argumentId : AllocId) (parentTag : BorTag) (argumentConcrete : pointer.provenance = .concrete argumentId parentTag)
    (argumentMetadata : DuplicatePrefixEmptyReferenceInput.Metadata before.memory argumentId (some parentTag))
    (argumentAbsent : before.memory.live.find? (fun row => row.1 == argumentId) = none)
    (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.pointer pointer) 0 count place := by
  by_cases zero : count = 0
  · subst count
    exact S03NonliveZeroContract.complete input tag concrete argumentId parentTag argumentConcrete argumentMetadata argumentAbsent
  · exact S03NonlivePositiveContract.complete input tag concrete argumentId parentTag argumentConcrete argumentMetadata argumentAbsent count zero

end
end DuplicatePrefix.S03NonliveConcreteContract
