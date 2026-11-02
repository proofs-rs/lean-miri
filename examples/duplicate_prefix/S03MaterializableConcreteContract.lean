import duplicate_prefix.S03MaterializableCall
import duplicate_prefix.S03MaterializablePreparedState
import duplicate_prefix.S03NonliveCallResources
import duplicate_prefix.S03SeparateLiveRawComplete

namespace DuplicatePrefix.S03MaterializableConcreteContract
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification S05ConsistentCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Original every-count safety for a materializable concrete empty argument
and arbitrary concrete return destination. The supported MEMORY/STATIC image
and finite relocations are selected by the original candidate; its actual lazy
prefix reduces to the local raw live driver, without a new prepared Contract
or a renewed whole-call work budget. -/
theorem complete {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (id : AllocId) (parentTag : BorTag) (concrete : pointer.provenance = .concrete id parentTag)
    (candidate : DuplicatePrefixEmptyReferenceInput.Materializable (imageContext options before input.contract.tracker)
      before.memory before.user.addresses id (some parentTag))
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance = .concrete input.contract.destination.id returnTag)
    (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.pointer pointer) 0 count place := by
  let facts := S03NonliveCallResources.of_contract input id parentTag concrete
  let original := input.contract.destination
  let model := input.contract.model
  have sameTracker : input.contract.tracker = original.tracker :=
    Option.some.inj (input.contract.runtime.enabled.symm.trans original.enabled)
  rw [sameTracker] at candidate
  have rootsBelow := input.contract.resources.cachedRootsBelow
  rw [sameTracker] at rootsBelow
  have tagMargin := input.contract.resources.tagRoom
  rw [sameTracker] at tagMargin
  obtain ⟨ctx,actualPointers⟩ := GlobalEmptyReferenceContext.exists_context options remaining span model.preciseOff model.implicitOff
  obtain ⟨packet,converted,attributes,callEq⟩ := S03MaterializableCall.concrete options limits remaining span ctx actualPointers
    model.debugOff model.nullComparator facts.dynamicFuel facts.validityFuel facts.dynamicEq facts.validityEq id parentTag
    original.tracker facts.base facts.offset count facts.nonzero before model.ghostOff model.shallow facts.cached original.enabled
    facts.first candidate rootsBelow model.noDataRace model.metadata input.slice_not_constructed place input.contract.thread
    input.contract.active input.contract.emptyHarnessCache
  have parentSame : parentTag = packet.root := by
    rcases packet.agreement with impossible | equal
    · cases impossible
    · exact Option.some.inj equal
  let prepared := GlobalEmptyRootCopy.preparedMachine options before id packet.root packet.source converted
  let destination := S03MaterializablePreparedState.input original id (some parentTag) packet converted
  let argumentEntry := GlobalEmptyRootCopy.entry packet.root packet.source converted
  have tagged : argumentEntry.allocation.extra.indexOfTag packet.root = some ⟨0⟩ := by
    simp [argumentEntry,GlobalEmptyRootCopy.entry,Allocation.mapExtra,BorrowTree.new,BorrowTree.indexOfTag,UniKeyMap.get]
    with_unfolding_all rfl
  let initial : S03SeparateLiveRawInstalledPacket.Initial options limits remaining span prepared pointer place := {
    model := S03MaterializablePreparedState.model model id packet.root packet.source converted remaining,
    destination := destination,runtime := facts.runtime,distinct := facts.distinct,order := facts.order,
    returnRoom := facts.headroom,first := facts.first,second := facts.second,tagMargin := tagMargin,
    argumentId := id,argumentEntry := argumentEntry,
    argumentLive := MemoryCopyBridge.live_lookup_replaced before.memory id argumentEntry,
    separate := S03MaterializableInput.separate packet original,
    parentTag := packet.root,
    argumentConcrete := concrete.trans (congrArg (fun tag => Provenance.concrete id tag) parentSame),
    nonnull := by rw [←facts.address];exact facts.nonzero,
    argumentBase := facts.base,argumentCached := facts.cached,
    argumentRuntime := S03MaterializablePreparedState.argument_runtime original facts.runtime id (some parentTag) packet,
    argumentMargin := by change 1+16<65536;decide,
    parent := ⟨0⟩,parentNode := GeneralBorrowFullSharedSeed.node packet.root,tagged := tagged,present := rfl,
    tag := returnTag,returnConcrete := returnConcrete,
    dynamicFuel := facts.dynamicFuel,validityFuel := facts.validityFuel,budget := facts.budget,
    dynamicEq := facts.dynamicEq,validityEq := facts.validityEq,dispatchEq := facts.dispatchEq,
    notConstructed := input.slice_not_constructed,
    extras := (S03MaterializablePreparedState.return_extras original id (some parentTag) packet converted).trans input.return_extras,
    thread := input.contract.thread,active := input.contract.active,noCache := input.contract.emptyHarnessCache }
  obtain ⟨installed,done,entry,trace,terminal,empty,noErrors,noUb,prefixSuccess⟩ := S03SeparateLiveRawComplete.complete initial count
  have normalized : Pointer.new (.concrete id parentTag) (Size.ofBytes (facts.base+facts.offset)) = pointer := by
    rw [facts.address]
    change (⟨pointer.offset,.concrete id parentTag⟩ : Pointer Provenance) = pointer
    rw [←concrete]
  rw [normalized] at callEq
  exact ⟨installed,done,callEq.trans entry,trace,terminal,empty,noErrors,noUb,prefixSuccess⟩

end
end DuplicatePrefix.S03MaterializableConcreteContract
