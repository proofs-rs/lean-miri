import duplicate_prefix.S03WildcardNonliveContract
import duplicate_prefix.S03WildcardMissContract
import duplicate_prefix.S03WildcardSameAllocationContract
import duplicate_prefix.S03WildcardArgumentSeparateContract
import duplicate_prefix.S03WildcardArgumentSeparateWildcardContract
import duplicate_prefix.S03MaterializableWildcardArgumentAllReturnContract

namespace DuplicatePrefix.S03WildcardContract
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
open DuplicatePrefixCallSpecification S05ConsistentCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Every original wildcard empty-argument call, for every count and return
provenance, executes initialization, the actual body and the original Return.
Candidate resolution and all live, nonlive, miss and supported image cases are
derived from the initial consistent contract. No selected Hit, successful
resolver operation, future borrow input or safety callback is a premise. -/
theorem complete {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (wildcard : pointer.provenance = .wildcard) (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.pointer pointer) 0 count place := by
  rcases S03WildcardNonliveContract.dispatch input wildcard count with miss | remainingHit | done
  · exact S03WildcardMissContract.complete_of_miss input wildcard miss count
  · obtain ⟨hit,live | image⟩ := remainingHit
    · obtain ⟨entry,present⟩ := live
      by_cases same : hit.id = input.contract.destination.id
      · exact S03WildcardSameAllocationContract.complete input wildcard hit same count
      · have separate : input.contract.destination.id ≠ hit.id := Ne.symm same
        cases provenance : input.contract.destination.pointer.provenance with
        | concrete id tag =>
          have binding := input.contract.destination.binding
          simp only [DuplicatePrefixReferenceInput.Binding,provenance] at binding
          have concrete : input.contract.destination.pointer.provenance = .concrete input.contract.destination.id tag :=
            provenance.trans (congrArg (fun id => Provenance.concrete id tag) binding.1)
          exact S03WildcardArgumentSeparateContract.complete input wildcard hit entry present separate tag concrete count
        | wildcard =>
          exact S03WildcardArgumentSeparateWildcardContract.complete input wildcard hit entry present separate provenance count
    · exact S03MaterializableWildcardArgumentAllReturnContract.complete input wildcard hit image.1 count
  · exact done

end
end DuplicatePrefix.S03WildcardContract
