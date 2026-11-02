import duplicate_prefix.S03WildcardLiveWildcardInstalledPacket
import duplicate_prefix.S03LiveWildcardPacketComplete
import duplicate_prefix.SuccessfulTraceTerminal

namespace DuplicatePrefix.S03WildcardLiveWildcardComplete
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Full original Result for EVERY count in the live wildcard empty argument,
same-allocation wildcard return case. Actual initialization produces all body
and Return premises; no future Input, operation success or safety certificate
is required from the caller. Case equations do not narrow Contract itself. -/
theorem complete
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (argumentWildcard : pointer.provenance = .wildcard)
    (hit : S03WildcardEmptyClassification.Hit (imageContext options before input.contract.tracker)
      before.memory before.user.addresses pointer.offset.bytes)
    (sameAllocation : hit.id = input.contract.destination.id)
    (returnWildcard : input.contract.destination.pointer.provenance = .wildcard)
    (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.pointer pointer) 0 count place := by
  obtain ⟨frame,machine,entry,⟨packet⟩⟩ := S03WildcardLiveWildcardInstalledPacket.enters input argumentWildcard hit sameAllocation returnWildcard count
  have nonnull := (S03WildcardEmptyClassification.candidate input.contract argumentWildcard).1
  obtain ⟨dynamicFuel,validityFuel,dynamicEq,validationEq⟩ := S03LiveEmptyContractData.fuels input.contract
  have positiveWork : 0 < work before 0 := by unfold work;omega
  have dispatch := input.contract.resources.executionFuel.1
  have dispatchEq : limits.callDispatch = (limits.callDispatch-1)+1 := by omega
  obtain ⟨done,trace,terminal,empty,noErrors,noUb⟩ := S03LiveWildcardPacketComplete.complete options limits remaining span frame machine place
    pointer.offset.bytes count packet nonnull validityFuel dynamicFuel (limits.callDispatch-1) dynamicEq dispatchEq
    input.contract.model.preciseOff input.contract.model.implicitOff input.contract.model.nullComparator input.contract.model.debugOff
    validationEq (DuplicatePrefixCallModel.sourceComparator _ _ _ _ input.contract.model)
  exact ⟨Storage.withCurrent #[] frame machine,done,entry,trace,terminal,empty,noErrors,noUb,
    SuccessfulTraceTerminal.prefix_step_success trace terminal⟩

/-- Initial Candidate classification executes the same-allocation live case
internally. Misses and other selected allocations remain explicit dispatcher
alternatives; no operation-success or branch-selection premise is added. -/
theorem dispatch
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (argumentWildcard : pointer.provenance = .wildcard)
    (returnWildcard : input.contract.destination.pointer.provenance = .wildcard)
    (count : UInt64) :
    before.user.addresses.allocIdFromAddr pointer.offset.bytes 0 (GlobalAddressLiveErrorExclusion.lookup before.memory) = .ok none ∨
      (∃ hit : S03WildcardEmptyClassification.Hit (imageContext options before input.contract.tracker)
          before.memory before.user.addresses pointer.offset.bytes, hit.id ≠ input.contract.destination.id) ∨
      DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.pointer pointer) 0 count place := by
  rcases S03WildcardEmptyClassification.contract input.contract argumentWildcard with miss | hits
  · exact Or.inl miss
  · obtain ⟨hit⟩ := hits
    by_cases same : hit.id = input.contract.destination.id
    · exact Or.inr (Or.inr (complete input argumentWildcard hit same returnWildcard count))
    · exact Or.inr (Or.inl ⟨hit,same⟩)

end
end DuplicatePrefix.S03WildcardLiveWildcardComplete
