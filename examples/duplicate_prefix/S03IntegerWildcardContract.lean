import duplicate_prefix.S03IntegerCallResources
import duplicate_prefix.S03IntegerWildcardZeroComplete
import duplicate_prefix.S03IntegerWildcardPositiveComplete

namespace DuplicatePrefix.S03IntegerWildcardContract
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
open DuplicatePrefixCallSpecification S05ConsistentCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Original integer/NoProv empty call, with an original wildcard destination,
for EVERY UInt64 count. The only input is the consistent initial contract and
its provenance branch; all intermediate inputs and operation successes are
derived by initStackFrame, the actual body, and the original Return rule. -/
theorem complete {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before} {address : UInt64}
    {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before (.integer address) 0 place)
    (wildcard : input.contract.destination.pointer.provenance = .wildcard) (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.integer address) 0 count place := by
  let packet := S03IntegerCallResources.of_contract input
  by_cases zero : count = 0
  · subst count
    exact S03IntegerWildcardZeroComplete.complete limits before input.contract.model place input.contract.destination
      packet.runtime packet.distinct packet.order packet.headroom packet.first packet.second wildcard address packet.nonzero
      packet.dynamicFuel packet.validityFuel packet.dynamicEq packet.validityEq input.slice_not_constructed input.return_extras
      input.contract.thread input.contract.active input.contract.emptyHarnessCache
  · exact S03IntegerWildcardPositiveComplete.complete limits before input.contract.model place input.contract.destination
      packet.runtime packet.distinct packet.order packet.headroom packet.first packet.second wildcard address count packet.nonzero zero
      packet.dynamicFuel packet.validityFuel packet.dynamicEq packet.validityEq packet.bodyFresh packet.bodyRoomNext
      packet.budget packet.dispatchEq input.slice_not_constructed input.return_extras input.contract.thread input.contract.active
      input.contract.emptyHarnessCache

end
end DuplicatePrefix.S03IntegerWildcardContract
