import duplicate_prefix.S03MaterializableCall
import duplicate_prefix.S03MaterializablePreparedState
import duplicate_prefix.S03WildcardArgumentSeparateComplete
import duplicate_prefix.S03WildcardArgumentResources

namespace DuplicatePrefix.S03MaterializableWildcardArgumentContract
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification S05ConsistentCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Original every-count safety for a materializable wildcard empty argument
hit and arbitrary concrete return destination. Actual lazy initialization is
followed by the general raw wildcard/live driver, using original local budgets. -/
theorem complete {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (wildcard : pointer.provenance = .wildcard)
    (hit : S03WildcardEmptyClassification.Hit (imageContext options before input.contract.tracker)
      before.memory before.user.addresses pointer.offset.bytes)
    (candidate : DuplicatePrefixEmptyReferenceInput.Materializable (imageContext options before input.contract.tracker)
      before.memory before.user.addresses hit.id none)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance = .concrete input.contract.destination.id returnTag)
    (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.pointer pointer) 0 count place := by
  let facts := S03WildcardArgumentResources.of_contract input wildcard
  let original := input.contract.destination
  let model := input.contract.model
  let offset := pointer.offset.bytes-hit.base
  have address : hit.base+offset = pointer.offset.bytes := by rw [UInt64.add_comm,UInt64.sub_add_cancel]
  have sameTracker : input.contract.tracker = original.tracker :=
    Option.some.inj (input.contract.runtime.enabled.symm.trans original.enabled)
  let argumentId := hit.id
  change DuplicatePrefixEmptyReferenceInput.Materializable (imageContext options before input.contract.tracker)
    before.memory before.user.addresses argumentId none at candidate
  rw [sameTracker] at candidate
  have rootsBelow := input.contract.resources.cachedRootsBelow
  rw [sameTracker] at rootsBelow
  have originalCandidate := S03WildcardEmptyClassification.candidate input.contract wildcard
  have allocLive := originalCandidate.2.coherent.live.2 hit.id (Array.contains_iff_mem.mp hit.exposed)
  obtain ⟨ctx,actualPointers⟩ := GlobalEmptyReferenceContext.exists_context options remaining span model.preciseOff model.implicitOff
  obtain ⟨packet,converted,attributes,callEq⟩ := S03MaterializableCall.wildcard options limits remaining span ctx actualPointers
    model.debugOff model.nullComparator facts.dynamicFuel facts.validityFuel facts.dynamicEq facts.validityEq hit.id original.tracker
    hit.base offset count (by rw [address];exact facts.nonnull) before model.ghostOff model.shallow hit.cached original.enabled
    facts.first candidate rootsBelow model.noDataRace hit.info hit.known facts.addressMode (by rw [address];exact hit.geometry)
    hit.exposed allocLive model.metadata input.slice_not_constructed place input.contract.thread input.contract.active input.contract.emptyHarnessCache
  let prepared := GlobalEmptyRootCopy.preparedMachine options before hit.id packet.root packet.source converted
  let destination := S03MaterializablePreparedState.input original hit.id none packet converted
  let argumentEntry := GlobalEmptyRootCopy.entry packet.root packet.source converted
  have infoEq : hit.info = ⟨packet.source.byteSize,packet.source.align,.liveData,packet.source.mutability⟩ :=
    Except.ok.inj (hit.known.symm.trans packet.alloc_info)
  have size : hit.info.size = packet.source.byteSize := congrArg AllocationInfo.size infoEq
  have entrySize : argumentEntry.allocation.byteSize = hit.info.size := attributes.size.trans size.symm
  have inverse : WildcardGeneralHitReborrow.Geometry prepared.user.addresses.intToPtrMap pointer.offset.bytes
      hit.base hit.id argumentEntry.allocation.byteSize := by
    rw [entrySize];exact hit.geometry
  let initial : S03WildcardArgumentSeparatePacket.Initial options limits remaining span prepared pointer place := {
    model := S03MaterializablePreparedState.model model hit.id packet.root packet.source converted remaining,
    destination := destination,runtime := facts.runtime,distinct := facts.distinct,order := facts.order,
    returnRoom := facts.returnRoom,first := facts.first,second := facts.second,tagMargin := facts.tagMargin,
    argumentId := hit.id,argumentEntry := argumentEntry,
    argumentLive := MemoryCopyBridge.live_lookup_replaced before.memory hit.id argumentEntry,
    separate := S03MaterializableInput.separate packet original,
    argumentWildcard := wildcard,nonnull := facts.nonnull,argumentBase := hit.base,argumentCached := hit.cached,
    addressMode := facts.addressMode,inverse := inverse,exposed := hit.exposed,
    argumentRuntime := S03MaterializablePreparedState.argument_runtime original facts.runtime hit.id none packet,
    argumentMargin := by change 1+16<65536;decide,tag := returnTag,returnConcrete := returnConcrete,
    dynamicFuel := facts.dynamicFuel,validityFuel := facts.validityFuel,budget := facts.budget,
    dynamicEq := facts.dynamicEq,validityEq := facts.validityEq,dispatchEq := facts.dispatchEq,
    notConstructed := input.slice_not_constructed,
    extras := (S03MaterializablePreparedState.return_extras original hit.id none packet converted).trans input.return_extras,
    thread := input.contract.thread,active := input.contract.active,noCache := input.contract.emptyHarnessCache }
  obtain ⟨installed,done,entry,trace,terminal,empty,noErrors,noUb,prefixSuccess⟩ := S03WildcardArgumentSeparateComplete.complete initial count
  have normalized : Pointer.new .wildcard (Size.ofBytes (hit.base+offset)) = pointer := by
    rw [address]
    change (⟨pointer.offset,.wildcard⟩ : Pointer Provenance) = pointer
    rw [←wildcard]
  rw [normalized] at callEq
  exact ⟨installed,done,callEq.trans entry,trace,terminal,empty,noErrors,noUb,prefixSuccess⟩

end
end DuplicatePrefix.S03MaterializableWildcardArgumentContract
