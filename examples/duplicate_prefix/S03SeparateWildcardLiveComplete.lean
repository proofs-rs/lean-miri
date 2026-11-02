import duplicate_prefix.S03SeparateWildcardLiveRawComplete

namespace DuplicatePrefix.S03SeparateWildcardLiveComplete
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- The original Contract supplies every local initial field needed by the
separate live argument/wildcard destination branch. Live lookup and concrete
argument provenance only select a case of the unchanged Candidate. -/
theorem initial
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (argumentId : AllocId) (argumentEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (argumentLive : before.memory.live.find? (fun row => row.1 == argumentId) = some (argumentId,argumentEntry))
    (separate : input.contract.destination.id ≠ argumentId)
    (parentTag : BorTag) (argumentConcrete : pointer.provenance = .concrete argumentId parentTag)
    (wildcard : input.contract.destination.pointer.provenance = .wildcard) :
    Nonempty (S03SeparateWildcardLiveRawInstalledPacket.Initial options limits remaining span before pointer place) := by
  obtain ⟨nonnull,base,parent,node,cached,tagged,present⟩ := S03ConcreteLiveCandidate.parent input.contract argumentId argumentEntry argumentLive parentTag argumentConcrete
  obtain ⟨argRuntime,argMargin⟩ := S03ConcreteLiveCandidate.runtime input.contract argumentId argumentEntry argumentLive
  obtain ⟨runtime,distinct,order,room,first,second⟩ := S03LiveEmptyContractData.resources input.contract
  obtain ⟨dynamicFuel,validityFuel,dynamicEq,validityEq⟩ := S03LiveEmptyContractData.fuels input.contract
  have same : input.contract.tracker=input.contract.destination.tracker :=
    Option.some.inj (input.contract.runtime.enabled.symm.trans input.contract.destination.enabled)
  have tagMargin := input.contract.resources.tagRoom
  rw [same] at tagMargin
  have positiveWork : 0 < work before 0 := by unfold work;omega
  have dispatch := input.contract.resources.executionFuel.1
  exact ⟨{
    model := input.contract.model,destination := input.contract.destination,runtime := runtime,distinct := distinct,order := order,
    returnRoom := by omega,first := first,second := second,tagMargin := tagMargin,
    argumentId := argumentId,argumentEntry := argumentEntry,argumentLive := argumentLive,separate := separate,
    parentTag := parentTag,argumentConcrete := argumentConcrete,nonnull := nonnull,argumentBase := base,argumentCached := cached,
    argumentRuntime := argRuntime,argumentMargin := argMargin,parent := parent,parentNode := node,tagged := tagged,present := present,
    wildcard := wildcard,dynamicFuel := dynamicFuel,validityFuel := validityFuel,budget := limits.callDispatch-1,
    dynamicEq := dynamicEq,validityEq := validityEq,dispatchEq := by omega,notConstructed := input.slice_not_constructed,
    extras := input.return_extras,thread := input.contract.thread,active := input.contract.active,noCache := input.contract.emptyHarnessCache }⟩

/-- Original Call, both actual MIR count branches and original wildcard Return,
with terminal/NoErrors/NoUB/prefix success for EVERY count in this LIVE case. -/
theorem complete
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (argumentId : AllocId) (argumentEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (argumentLive : before.memory.live.find? (fun row => row.1 == argumentId) = some (argumentId,argumentEntry))
    (separate : input.contract.destination.id ≠ argumentId)
    (parentTag : BorTag) (argumentConcrete : pointer.provenance = .concrete argumentId parentTag)
    (wildcard : input.contract.destination.pointer.provenance = .wildcard) (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.pointer pointer) 0 count place := by
  obtain ⟨s⟩ := initial input argumentId argumentEntry argumentLive separate parentTag argumentConcrete wildcard
  exact S03SeparateWildcardLiveRawComplete.complete s count

end
end DuplicatePrefix.S03SeparateWildcardLiveComplete
