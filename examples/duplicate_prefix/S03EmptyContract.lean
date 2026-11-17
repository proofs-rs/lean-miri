import duplicate_prefix.S03IntegerZeroContract
import duplicate_prefix.S03IntegerPositiveContract
import duplicate_prefix.S03IntegerWildcardContract
import duplicate_prefix.S03ConcreteEmptyDispatch
import duplicate_prefix.S03ConcreteLiveWildcardComplete
import duplicate_prefix.S03SeparateWildcardLiveComplete
import duplicate_prefix.S03MaterializableConcreteAllReturns
import duplicate_prefix.S03WildcardNonliveContract
import duplicate_prefix.S03WildcardMissContract
import duplicate_prefix.S03WildcardSameAllocationContract
import duplicate_prefix.S03WildcardArgumentSeparateContract
import duplicate_prefix.S03WildcardArgumentSeparateWildcardContract
import duplicate_prefix.S03MaterializableWildcardArgumentAllReturnContract

namespace DuplicatePrefix.S03EmptyContract
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
open DuplicatePrefixCallSpecification S05ConsistentCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Every empty argument representation and every count/return-provenance
case in the explicit consistent initial domain satisfies the original actual
call Result. Candidate classification, initialization, body and Return are
proved internally; no branch-success callback or safety premise is assumed.
This is the len=0 theorem. Positive lengths, ordinary-valid-input coverage,
and the original unrefined Contract/Target remain separate obligations. -/
theorem complete {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {argument : DuplicatePrefixSliceArgument.Argument} {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before argument 0 place)
    (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument 0 count place := by
  cases argument with
  | integer address =>
    cases provenance : input.contract.destination.pointer.provenance with
    | concrete id tag =>
      have binding := input.contract.destination.binding
      simp only [DuplicatePrefixReferenceInput.Binding,provenance] at binding
      have concrete : input.contract.destination.pointer.provenance = .concrete input.contract.destination.id tag :=
        provenance.trans (congrArg (fun id => Provenance.concrete id tag) binding.1)
      by_cases zero : count = 0
      · subst count
        exact S03IntegerZeroContract.complete input tag concrete
      · exact S03IntegerPositiveContract.complete input tag concrete count zero
    | wildcard => exact S03IntegerWildcardContract.complete input provenance count
  | pointer pointer =>
    cases argumentProvenance : pointer.provenance with
    | concrete id tag =>
      rcases S03ConcreteEmptyDispatch.dispatch input id tag argumentProvenance count with live | image | done
      · obtain ⟨⟨state⟩,wildcard⟩ := live
        by_cases same : id = input.contract.destination.id
        · have argumentConcrete : pointer.provenance = .concrete input.contract.destination.id tag :=
            argumentProvenance.trans (congrArg (fun id => Provenance.concrete id tag) same)
          exact S03ConcreteLiveWildcardComplete.complete input tag argumentConcrete wildcard count
        · exact S03SeparateWildcardLiveComplete.complete input id state.entry state.live (Ne.symm same)
            tag argumentProvenance wildcard count
      · exact S03MaterializableConcreteAllReturns.complete input id tag argumentProvenance image.1 count
      · exact done
    | wildcard =>
      rcases S03WildcardNonliveContract.dispatch input argumentProvenance count with miss | remainingHit | done
      · exact S03WildcardMissContract.complete_of_miss input argumentProvenance miss count
      · obtain ⟨hit,live | image⟩ := remainingHit
        · obtain ⟨entry,present⟩ := live
          by_cases same : hit.id = input.contract.destination.id
          · exact S03WildcardSameAllocationContract.complete input argumentProvenance hit same count
          · have separate : input.contract.destination.id ≠ hit.id := Ne.symm same
            cases provenance : input.contract.destination.pointer.provenance with
            | concrete id tag =>
              have binding := input.contract.destination.binding
              simp only [DuplicatePrefixReferenceInput.Binding,provenance] at binding
              have concrete : input.contract.destination.pointer.provenance = .concrete input.contract.destination.id tag :=
                provenance.trans (congrArg (fun id => Provenance.concrete id tag) binding.1)
              exact S03WildcardArgumentSeparateContract.complete input argumentProvenance hit entry present separate tag concrete count
            | wildcard =>
              exact S03WildcardArgumentSeparateWildcardContract.complete input argumentProvenance hit entry present separate provenance count
        · exact S03MaterializableWildcardArgumentAllReturnContract.complete input argumentProvenance hit image.1 count
      · exact done

end
end DuplicatePrefix.S03EmptyContract
