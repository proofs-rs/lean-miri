import duplicate_prefix.S03MaterializableWildcardArgumentContract
import duplicate_prefix.S03MaterializableWildcardArgumentWildcardReturnContract

namespace DuplicatePrefix.S03MaterializableWildcardArgumentAllReturnContract
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
open DuplicatePrefixCallSpecification S05ConsistentCallSpecification
set_option autoImplicit false
noncomputable section

/-- Every original return provenance and count for a selected materializable
wildcard empty-argument hit. Both cases execute the actual image prefix and
original call; only initial Candidate metadata is added to its branch. -/
theorem complete {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (wildcard : pointer.provenance = .wildcard)
    (hit : S03WildcardEmptyClassification.Hit (imageContext options before input.contract.tracker)
      before.memory before.user.addresses pointer.offset.bytes)
    (candidate : DuplicatePrefixEmptyReferenceInput.Materializable (imageContext options before input.contract.tracker)
      before.memory before.user.addresses hit.id none)
    (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.pointer pointer) 0 count place := by
  cases provenance : input.contract.destination.pointer.provenance with
  | concrete id tag =>
    have binding := input.contract.destination.binding
    simp only [DuplicatePrefixReferenceInput.Binding,provenance] at binding
    have concrete : input.contract.destination.pointer.provenance = .concrete input.contract.destination.id tag :=
      provenance.trans (congrArg (fun id => Provenance.concrete id tag) binding.1)
    exact S03MaterializableWildcardArgumentContract.complete input wildcard hit candidate tag concrete count
  | wildcard => exact S03MaterializableWildcardArgumentWildcardReturnContract.complete input wildcard hit candidate provenance count

end
end DuplicatePrefix.S03MaterializableWildcardArgumentAllReturnContract
