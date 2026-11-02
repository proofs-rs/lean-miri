import duplicate_prefix.S03ConcreteEmptyDispatch
import duplicate_prefix.S03ConcreteLiveWildcardComplete
import duplicate_prefix.S03SeparateWildcardLiveComplete
import duplicate_prefix.S03MaterializableConcreteAllReturns

namespace DuplicatePrefix.S03ConcreteContract
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
open DuplicatePrefixCallSpecification S05ConsistentCallSpecification
set_option autoImplicit false
noncomputable section

/-- The original concrete empty-argument family, every count and every return
provenance. The original Candidate is classified internally; live/nonlive/image
selection, physical metadata, numeric resources and all execution/safety facts
are derived. No case-success callback or additional caller field is assumed. -/
theorem complete {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (id : AllocId) (tag : BorTag) (concrete : pointer.provenance = .concrete id tag)
    (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.pointer pointer) 0 count place := by
  rcases S03ConcreteEmptyDispatch.dispatch input id tag concrete count with live | image | done
  · obtain ⟨⟨state⟩,wildcard⟩ := live
    by_cases same : id = input.contract.destination.id
    · have argumentConcrete : pointer.provenance = .concrete input.contract.destination.id tag :=
        concrete.trans (congrArg (fun id => Provenance.concrete id tag) same)
      exact S03ConcreteLiveWildcardComplete.complete input tag argumentConcrete wildcard count
    · exact S03SeparateWildcardLiveComplete.complete input id state.entry state.live (Ne.symm same)
        tag concrete wildcard count
  · exact S03MaterializableConcreteAllReturns.complete input id tag concrete image.1 count
  · exact done

end
end DuplicatePrefix.S03ConcreteContract
