import duplicate_prefix.S03IntegerZeroComplete
import duplicate_prefix.S03IntegerCallResources

namespace DuplicatePrefix.S03IntegerZeroContract
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification S05ConsistentCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- A complete case of the revised initial-data specification: provenance-free
empty input, count zero, and an arbitrary concrete physical return pointer.
The conclusion is the original actual-call result, including every reachable
successful finite prefix. Initial consistency is the explicit wrapper domain;
this theorem does not claim the unrefined Contract or all argument cases. -/
theorem complete {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before} {address : UInt64}
    {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before (.integer address) 0 place)
    (tag : BorTag) (concrete : input.contract.destination.pointer.provenance = .concrete input.contract.destination.id tag) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.integer address) 0 0 place := by
  let facts := S03IntegerCallResources.of_contract input
  exact S03IntegerZeroComplete.complete limits before input.contract.model place input.contract.destination
    facts.runtime facts.distinct facts.order facts.headroom facts.first facts.second tag concrete address facts.nonzero
    facts.dynamicFuel facts.validityFuel facts.dynamicEq facts.validityEq input.slice_not_constructed input.return_extras
    input.contract.thread input.contract.active input.contract.emptyHarnessCache

end
end DuplicatePrefix.S03IntegerZeroContract
