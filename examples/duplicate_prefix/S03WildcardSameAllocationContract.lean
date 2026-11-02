import duplicate_prefix.S03WildcardLiveComplete
import duplicate_prefix.S03WildcardLiveWildcardComplete

namespace DuplicatePrefix.S03WildcardSameAllocationContract
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
open DuplicatePrefixCallSpecification S05ConsistentCallSpecification
set_option autoImplicit false
noncomputable section

/-- A selected live wildcard empty argument sharing the original destination
allocation executes the original call for every count and return provenance.
The selected Hit is initial Candidate metadata, not an operation-success input. -/
theorem complete {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (wildcard : pointer.provenance = .wildcard)
    (hit : S03WildcardEmptyClassification.Hit (imageContext options before input.contract.tracker)
      before.memory before.user.addresses pointer.offset.bytes)
    (sameAllocation : hit.id = input.contract.destination.id)
    (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.pointer pointer) 0 count place := by
  cases provenance : input.contract.destination.pointer.provenance with
  | concrete id tag =>
    have binding := input.contract.destination.binding
    simp only [DuplicatePrefixReferenceInput.Binding,provenance] at binding
    have concrete : input.contract.destination.pointer.provenance = .concrete input.contract.destination.id tag :=
      provenance.trans (congrArg (fun id => Provenance.concrete id tag) binding.1)
    exact S03WildcardLiveComplete.complete input wildcard hit sameAllocation tag concrete count
  | wildcard => exact S03WildcardLiveWildcardComplete.complete input wildcard hit sameAllocation provenance count

end
end DuplicatePrefix.S03WildcardSameAllocationContract
