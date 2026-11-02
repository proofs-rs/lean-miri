import duplicate_prefix.S02WildcardSameDestinationRejectedInitial
import duplicate_prefix.S02WildcardRejectedSiteFrame
import duplicate_prefix.S02WildcardRejectedSiteSlots
import duplicate_prefix.S02SeparateDestinationRejectedPurePrefix
import duplicate_prefix.S02SameDestinationAcceptedGuardLedger
import duplicate_prefix.S02WildcardAcceptedSiteSlots
import duplicate_prefix.S02SameDestinationAcceptedResult
import duplicate_prefix.S02WildcardSameDestinationAcceptedPhysical
import duplicate_prefix.S02SameDestinationRejectedResultOrder
import duplicate_prefix.S02SameDestinationRejectedResultLookup
import duplicate_prefix.S02SameDestinationRejectedResultLiteralActivity
import duplicate_prefix.S02SameDestinationRejectedPhysicalTransport
import duplicate_prefix.S02DisjointSharedLenLiteral
import duplicate_prefix.S02HiddenLeafActiveRelease
import duplicate_prefix.S03ActiveSameReturnStepBounds
import duplicate_prefix.DuplicatePrefixArgumentCallResult
import duplicate_prefix.SuccessfulTraceTerminal
import duplicate_prefix.S02WildcardPositiveIdUnique
namespace DuplicatePrefix.S02WildcardSameDestinationAcceptedResult
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- The unchanged call contract executes the accepted branch for a wildcard
source and concrete return place in the same resolved allocation. -/
theorem result
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance} (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance = .concrete input.contract.destination.id returnTag)
    (countPositive : (0 : UInt64) < count) (within : count ≤ len/2) :
    ∃ reference : DuplicatePrefixReferenceInput.Positive before (Pointer.new .wildcard (Size.ofBytes address)) len,
      reference.id = input.contract.destination.id →
      DuplicatePrefixArgumentCallResult.Result options limits remaining span before
        (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len count place := by
  obtain ⟨reference,ready⟩ := S02WildcardSameDestinationRejectedInitial.enters address len count input nonempty returnTag returnConcrete
  refine ⟨reference,?_⟩
  intro sameId
  obtain ⟨entry,machine,packet,raw,actual,sourceId,sourceTag,sourceOffset,sourceLen,sourceSame,
    rawTag,rawParent,rawSelected,rawMaximum,rawOffset,rawLen,initialOrder,capacity,nodes,nodeRoom,tagRoom,
    reserve,tagReserve,frameLiteral,rawUser,rawThreads,rawRace,mode⟩ := ready sameId
  let tracker := packet.tracker
  let sourceEntry := packet.destination.entry
  change sourceEntry.allocation.extra.nodes.size+8 < 65536 at reserve
  change tracker.global.nextPointerTag.value.toNat+7 < 18446744073709551615 at tagReserve
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag) (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
  have frameMetadata := PositiveRootInstalledFrame.metadata root adjusted count {} reference.id reference.tracker.global.nextPointerTag packet.destination.id packet.returnTag
  have slots := PositiveRootInstalledFrame.slot_option root (RawRootInvocation.locals before place input.contract.model.noDataRace)
    adjusted count {} reference.id reference.tracker.global.nextPointerTag packet.destination.id packet.returnTag
  have initialSize : entry.locals.size = 25 := by rw [frameLiteral];exact PositiveRootInstalledFrame.size _ _ _ _ _ _ _ _
  have initialBody : entry.body = RootBody.reflected.body.body := by rw [frameLiteral];exact frameMetadata.1
  have initialIdentity : entry.bodyIdentity = RootBody.reflected.body.identity := by rw [frameLiteral];exact frameMetadata.2.1
  have initialCallee : entry.functionInstance = RootBody.reflected.functionInstance := by rw [frameLiteral];exact frameMetadata.2.2.1
  have initialLocation : entry.location = .mir ⟨0,0⟩ := by rw [frameLiteral];exact frameMetadata.2.2.2.2.2.2.2.2
  have initialClocks : entry.extra.dataRace = none := by rw [frameLiteral];exact frameMetadata.2.2.2.2.2.2.1.trans root.noClocks
  have initialAll : CopyHelperCleanup.AllImmediate entry := by
    rw [frameLiteral];exact PositiveRootInstalledFrame.immediate root (RawRootInvocation.locals before place input.contract.model.noDataRace) _ _ _ _ _ _ _
  obtain ⟨rawMemory,rawBorrow,rawRace0,rawAddresses,rawGhost,rawShallow,rawTypes,rawBackend,rawExtras⟩ := RawRootInvocation.preservation #[] before
  have machineGhost : machine.user.payload.ghost = false := by rw [rawUser,rawGhost];exact input.contract.model.ghostOff
  have machineShallow : machine.user.payload.validation = .Shallow := by rw [rawUser,rawShallow];exact input.contract.model.shallow
  have machineUnchecked : ((config options (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false := by
    rw [rawUser,RootZeroInvocationState.raw_control];exact input.contract.model.unchecked
  have machineNoGc : ((config options (remaining+1) span).terminators.getControl machine.user).gcInterval = 0 := by
    rw [rawUser,RootZeroInvocationState.raw_control];exact input.contract.model.noGc
  have machineFixed : machine.threads.fixedScheduling = true := by rw [rawThreads];exact input.contract.model.fixedScheduler
  have validationPositive : 0 < options.limits.validation := by have h:=input.contract.resources.configuredFuel.2.2.2;unfold work at h;omega
  have dynamicPositive : 0 < options.place.dynamicFuel := by have h:=input.contract.resources.dynamicFuel;unfold work at h;omega
  have dispatchPositive : 0 < limits.callDispatch := by have h:=input.contract.resources.executionFuel.1;unfold work at h;omega
  have countNonzero : count ≠ 0 := by intro zero;rw [zero] at countPositive;exact UInt64.lt_irrefl 0 countPositive
  obtain ⟨frame,prefixTrace,shape⟩ := S02SeparateDestinationRejectedPurePrefix.executes_from_installed_locals options limits remaining span
    (DuplicatePrefixCallModel.sourceComparator options remaining span before input.contract.model) input.contract.model.debugOff
    (options.limits.validation-1) (Nat.sub_add_cancel validationPositive).symm entry machine count countNonzero
    initialBody initialIdentity initialCallee initialLocation initialSize adjusted (by intro i;rw [frameLiteral];exact slots i)
    initialClocks initialAll tracker packet.enabled mode machineGhost machineShallow machineUnchecked machineNoGc machineFixed
  let current := RootZeroCompleteState.tick options remaining span machine
  obtain ⟨tickMemory,tickTracker,tickRace,tickThreads,tickAddresses,tickTypes,tickBackend,tickExtras⟩ := S02SeparateDestinationTickLedger.preserved options remaining span machine
  have enabled : current.borrowTracker = some tracker := by rw [tickTracker];exact packet.enabled
  have live : current.memory.live.find? (fun row => row.1 == reference.id) = some (reference.id,sourceEntry) := by rw [tickMemory,←sourceId];exact packet.destination.live
  have cached : current.user.addresses.baseAddr.find? (fun row => row.allocId == reference.id) =
      some ⟨reference.id,reference.base⟩ := by
    rw [tickAddresses,rawUser,rawAddresses]
    exact reference.cachedBase
  have types : current.user.payload.payload.user.types = before.user.payload.payload.user.types := by
    rw [tickTypes,rawUser,rawTypes]
  have metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] frame current)).metadata =
      PreparedReflection.actual.runtime := by
    change current.user.payload.payload.user.types.metadata = _
    rw [types]; exact input.contract.model.metadata
  have notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] frame current)).entries.any (·.value.ty == 4) = false := by
    change current.user.payload.payload.user.types.entries.any (·.value.ty == 4) = _
    rw [types]; exact input.slice_not_constructed
  have positive : (0 : UInt64) < len := by
    apply UInt64.lt_iff_toNat_lt.mpr
    have := reference.storage.positive
    exact this
  have nonzero : reference.base+reference.offset ≠ 0 := by
    rw [←reference.pointerAddress]; exact reference.nonnull
  have signedFits : len.toNat < 9223372036854775808 := reference.storage.signedSize
  have fresh : tracker.global.nextPointerTag.value < 18446744073709551615 := raw.tagRoom
  have shortRoom : sourceEntry.allocation.extra.nodes.size+2 < 65536 := nodes
  have nodeRoom : sourceEntry.allocation.extra.nodes.size+2 ≤ 4294967295 := by omega
  obtain ⟨body,identity,callee,located,size,noClocks,sourceCell,lenCell,exprCell,immediate⟩ :=
    S02WildcardRejectedSiteFrame.of_shape options remaining span before place
      input.contract.model.noDataRace address len reference count packet.destination.id
      packet.returnTag entry frame frameLiteral shape
  obtain ⟨slot0,slot13,slot15,slot16,slot7,slot8,slot9,slot10⟩ :=
    S02WildcardAcceptedSiteSlots.from_shape address len count input reference
      packet.destination.id packet.returnTag entry frame frameLiteral shape
  have validSource : (1 : MIR.LocalId) < frame.locals.size := by rw [size]; decide
  have validDest : RootReferenceFacts.destination true < frame.locals.size := by rw [size]; decide
  have valid11 : 11 < frame.locals.size := by rw [size]; decide
  have sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
        (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm) := by
    have h := congrArg LocalState.value (Option.some.inj
      (by simpa [Array.getElem?_eq_getElem validSource] using sourceCell))
    rw [CanonicalConfigFacts.actual_access_runtime options () remaining span,
      CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span] at *
    exact h
  have sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference := by
    exact congrArg LocalState.layout (Option.some.inj
      (by simpa [Array.getElem?_eq_getElem validSource] using sourceCell))
  have lenLive : frame.locals[11].value = .live (.immediate .uninit) := by
    exact congrArg LocalState.value (Option.some.inj
      (by simpa [Array.getElem?_eq_getElem valid11] using lenCell))
  have lenUncached : frame.locals[11].layout = none := by
    exact congrArg LocalState.layout (Option.some.inj
      (by simpa [Array.getElem?_eq_getElem valid11] using lenCell))
  have destCellValid : (12 : MIR.LocalId) < frame.locals.size := by rw [size]; decide
  have destLive : frame.locals[RootReferenceFacts.destination true].value = .live (.immediate .uninit) := by
    have h := congrArg LocalState.value (Option.some.inj
      (by simpa [Array.getElem?_eq_getElem destCellValid] using exprCell))
    simpa [RootReferenceFacts.destination] using h
  have destUncached : frame.locals[RootReferenceFacts.destination true].layout = none := by
    have h := congrArg LocalState.layout (Option.some.inj
      (by simpa [Array.getElem?_eq_getElem destCellValid] using exprCell))
    simpa [RootReferenceFacts.destination] using h
  have noClocks' : frame.extra.dataRace = none := noClocks
  have ghost : current.user.payload.ghost = false := by
    rw [RootZeroCompleteState.tick_ghost,rawUser,rawGhost]
    exact input.contract.model.ghostOff
  have shallow : current.user.payload.validation = .Shallow := by
    rw [RootZeroCompleteState.tick_shallow,rawUser,rawShallow]
    exact input.contract.model.shallow
  have race : current.dataRace = none := by
    rw [tickRace,rawRace,rawRace0]; exact input.contract.model.noDataRace
  have backend : current.user.payload.payload.user.backend = .none := by
    rw [tickBackend,rawUser,rawBackend]; exact input.contract.model.noBackend
  have unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl current.user).checkedArithmetic = false := by
    rw [(RootZeroCompleteState.tick_flags options remaining span machine).1,rawUser,RootZeroInvocationState.raw_control]
    exact input.contract.model.unchecked
  have noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl current.user).gcInterval = 0 := by
    rw [(RootZeroCompleteState.tick_flags options remaining span machine).2,rawUser,RootZeroInvocationState.raw_control]
    exact input.contract.model.noGc
  have fixed : current.threads.fixedScheduling = true := by
    rw [tickThreads,rawThreads]
    change before.threads.fixedScheduling = true
    exact input.contract.model.fixedScheduler
  have rawActive : (RawRootInvocation.machine #[] before).threads.activeThread? =
      some {input.contract.thread with topUserRelevantFrame := some 0} := by
    change (CallEntryFacts.cacheTop (CallEntryFacts.freshRoot before).1 0).threads.activeThread? = _
    exact AsMutPushPreserves.active_cache (CallEntryFacts.freshRoot before).1 input.contract.thread
      (by simpa only [CallEntryFacts.freshRoot] using input.contract.active) 0
  have active : current.threads.activeThread? =
      some {input.contract.thread with topUserRelevantFrame := some 0} := by
    rw [tickThreads,rawThreads]; exact rawActive
  let thread := {input.contract.thread with topUserRelevantFrame := some 0}
  have topZero : ({input.contract.thread with topUserRelevantFrame := some 0}).topUserRelevantFrame = some 0 := rfl
  have bothRaw : DuplicatePrefixBorrowAuthorization.Positive sourceEntry.allocation.extra tracker.global.protectedTags
      (some raw.parent) (some raw.selected) raw.maximum reference.offset len := by
    simpa only [rawParent,rawSelected,rawMaximum,sourceOffset,sourceLen] using packet.sourcePositive
  have activityRaw : GeneralBorrowFreshActiveWithin.ActiveWithin sourceEntry.allocation.extra raw.parent .Write reference.offset (reference.offset+len) := by
    simpa only [rawParent,sourceOffset,sourceLen] using packet.sourceActivity
  have cell (n : Fin 25) : n.val < frame.locals.size := by rw [size];exact n.isLt
  have fromSlot (n : Fin 25) (value : LocalState Provenance LocalLayout) (h : frame.locals[n.val]? = some value) :
      frame.locals[n.val]'(cell n) = value := Option.some.inj ((Array.getElem?_eq_getElem (cell n)).symm.trans h)
  obtain ⟨guard,post,guardTree,held,child,acceptedTrace,locationAfter,sizeAfter,bodyAfter,identityAfter,
    calleeAfter,extraAfter,placeAfter,continuationAfter,varargsAfter,localsIdentityAfter,trackAfter,
    zeroAfter,sourceAfter,countAfter,flagAfter,slot15After,slot16After,highAfter,allAfter,
    memoryAfter,trackedAfter,modeAfter,runtimeAfter,readAfter,bothAfter,activityAfter,graphAfter,
    ghostAfter,shallowAfter,raceAfter,addressesAfter,typesAfter,extrasAfter,backendAfter,uncheckedAfter,noGcAfter,
    fixedAfter,finalThread,finalActive,finalTop,treeLiteral⟩ :=
    S02SameDestinationAcceptedGuardLedger.complete options limits remaining span
      input.contract.model.preciseOff input.contract.model.implicitOff input.contract.model.debugOff
      input.contract.model.nullComparator (options.place.dynamicFuel-1) (options.limits.validation-1)
      (Nat.sub_add_cancel dynamicPositive).symm (Nat.sub_add_cancel validationPositive).symm
      reference.base reference.offset len reference.id sourceEntry positive nonzero signedFits #[] frame current
      body identity callee located tracker enabled mode fresh reference.tracker.global.nextPointerTag
      packet.sourceRuntime raw (rawTag.trans sourceTag) rawOffset rawLen capacity validSource validDest sourceLive sourceCached
      destLive destUncached noClocks ghost shallow cached live race metadata notConstructed
      shortRoom nodeRoom tagRoom rfl (limits.callDispatch-1) (Nat.sub_add_cancel dispatchPositive).symm
      (DuplicatePrefixCallModel.sourceComparator options remaining span before input.contract.model)
      valid11 lenLive lenUncached backend unchecked noGc fixed
      {input.contract.thread with topUserRelevantFrame := some 0} active topZero
      count countPositive within size
      (congrArg LocalState.value (fromSlot ⟨13,by decide⟩ _ slot13))
      (congrArg LocalState.layout (fromSlot ⟨13,by decide⟩ _ slot13))
      (congrArg LocalState.value (fromSlot ⟨0,by decide⟩ _ slot0))
      (congrArg LocalState.layout (fromSlot ⟨0,by decide⟩ _ slot0))
      (congrArg LocalState.value (fromSlot ⟨7,by decide⟩ _ slot7))
      (congrArg LocalState.layout (fromSlot ⟨7,by decide⟩ _ slot7))
      (congrArg LocalState.value (fromSlot ⟨15,by decide⟩ _ slot15))
      (congrArg LocalState.layout (fromSlot ⟨15,by decide⟩ _ slot15))
      (congrArg LocalState.value (fromSlot ⟨16,by decide⟩ _ slot16))
      (congrArg LocalState.layout (fromSlot ⟨16,by decide⟩ _ slot16))
      (congrArg LocalState.value (fromSlot ⟨8,by decide⟩ _ slot8))
      (congrArg LocalState.layout (fromSlot ⟨8,by decide⟩ _ slot8))
      (congrArg LocalState.value (fromSlot ⟨9,by decide⟩ _ slot9))
      (congrArg LocalState.layout (fromSlot ⟨9,by decide⟩ _ slot9))
      (congrArg LocalState.value (fromSlot ⟨10,by decide⟩ _ slot10))
      (congrArg LocalState.layout (fromSlot ⟨10,by decide⟩ _ slot10))
      immediate bothRaw activityRaw
  obtain ⟨oldNode,oldPresent,oldTag,oldParent,oldHidden,oldTagged⟩ := graphAfter.oldNodes packet.sourceChild packet.sourceNode packet.sourcePresent
  have guardSourceTagged : guardTree.indexOfTag raw.parentTag = some raw.parent := by simpa only [rawTag,rawParent,sourceSame] using oldTagged
  have sourcePresent : guardTree.nodeAt raw.parent = some oldNode := by simpa only [rawParent] using oldPresent
  have sourceHidden : oldNode.isExposed = false := oldHidden.trans packet.sourceHidden
  have heldTagRoom : held.global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    have growth := graphAfter.tagCounter
    have bound : held.global.nextPointerTag.value.toNat < 18446744073709551615 := by omega
    simpa using bound
  let mutableRaw : GeneralBorrowRawDefault.Input guardTree held.global := {
    parentTag := raw.parentTag,parent := raw.parent,selected := raw.selected,maximum := raw.maximum,
    offset := reference.offset,len := len,tagged := guardSourceTagged,positive := Classical.choice bothAfter,
    distinct := graphAfter.distinct,order := graphAfter.order,short := graphAfter.short,
    nodeRoom := by have h:=graphAfter.short;omega,tagRoom := heldTagRoom }
  have headroom : guardTree.nodes.size+2 < 65536 := by have growth:=graphAfter.growth;omega
  have tagsRoom : held.global.nextPointerTag.value.toNat+1 < 18446744073709551615 := by have growth:=graphAfter.tagCounter;omega
  have guardCapacity : guardTree.locations.size = sourceEntry.allocation.byteSize := graphAfter.capacity.trans capacity
  have literalEq : guardTree = GeneralBorrowRawSharedToLenLiteralLedger.finalTree sourceEntry.allocation.extra tracker raw.parentTag raw.offset raw.len raw.tagRoom := by
    simpa only [rawTag,sourceTag,rawOffset,rawLen] using treeLiteral
  have guardOrder : GeneralBorrowWildcardParentTagOrder.ParentTagOrder guardTree := by
    rw [literalEq]
    exact S02SameDestinationRejectedResultOrder.literal sourceEntry.allocation.extra tracker reference.id packet.sourceRuntime raw nodes nodeRoom tagRoom initialOrder
  have guardLive : post.memory.live.find? (fun row => row.1 == reference.id) =
      some (reference.id,{sourceEntry with allocation := sourceEntry.allocation.setExtra guardTree}) := by
    rw [memoryAfter];exact MemoryCopyBridge.live_lookup_replaced _ _ _
  have guardCached : post.user.addresses.baseAddr.find? (fun row => row.allocId == reference.id) = some ⟨reference.id,reference.base⟩ := by rw [addressesAfter];exact cached
  have guardMetadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] guard post)).metadata = PreparedReflection.actual.runtime := by
    change post.user.payload.payload.user.types.metadata = _
    rw [typesAfter];exact metadata
  have guardNotConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] guard post)).entries.any (·.value.ty == 4) = false := by
    change post.user.payload.payload.user.types.entries.any (·.value.ty == 4) = _
    rw [typesAfter];exact notConstructed
  have sourceExtras : post.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == reference.id) = some (reference.id,⟨none,#[]⟩) := by
    rw [extrasAfter,tickExtras,rawUser,rawExtras,←sourceId,sourceId,sameId]
    exact input.return_extras
  obtain ⟨sizeEq,lenEq,storage,mutable,storageFits,maskValid,maskLength,initialized,cleared⟩ :=
    S02WildcardSameDestinationAcceptedPhysical.at_actual_call address len count input nonempty returnTag returnConcrete
      reference sameId entry machine sourceEntry actual (by rw [←sourceId];exact packet.destination.live)
  have bounds : reference.offset.toNat+len.toNat ≤ sourceEntry.allocation.byteSize.bytes.toNat := by rw [sizeEq,reference.size];exact reference.storage.bounds
  have snapshotLen : (AllocationCopy.snapshot reference.entry.allocation).size = reference.entry.allocation.len := by
    cases reference.entry.allocation
    simp [AllocationCopy.snapshot,Allocation.inspectWithUninitAndPtrOutsideInterpreter,Allocation.len,Pure.pure,Except.pure,Except.toOption,Option.getD]
  have initialFits : reference.entry.allocation.len < 2^64 := by rw [reference.bytes];exact reference.capacity.toNat_lt
  have returnFits : input.contract.destination.offset.toNat+1 < 2^64 := by have := input.contract.destination.bounds;have := input.contract.destination.capacity.toNat_lt;omega
  have endpoint := DuplicatePrefix.source_end (Size.ofBytes input.contract.destination.offset) 1 (by simpa only [Size.ofBytes,UInt64.toNat_one] using returnFits)
  have direct := S02SameDestinationUninitProvenanceResult.after_clear reference.entry.allocation.provenanceMap sourceEntry.allocation.provenanceMap
    (allocRange (Size.ofBytes input.contract.destination.offset) (Size.ofBytes 1)) (Size.ofBytes (input.contract.destination.offset+1))
    (AllocationCopy.snapshot reference.entry.allocation) (by simpa only [snapshotLen] using reference.provenanceMap)
    (by change (1 : UInt64) ≠ 0;decide) endpoint (by simpa only [snapshotLen] using initialFits) cleared
  have currentDirect : S02SameDestinationUninitProvenanceInput.DirectInput sourceEntry.allocation.provenanceMap sourceEntry.allocation.len := by simpa only [snapshotLen,←lenEq] using direct
  have sourceMaskLen : sourceEntry.allocation.initializationMask.len = sourceEntry.allocation.byteSize :=
    maskLength.trans (reference.storage.maskLength.trans (reference.size.symm.trans sizeEq.symm))
  have sumFits : reference.offset.toNat+len.toNat < 2^64 := by have := sourceEntry.allocation.byteSize.bytes.toNat_lt;omega
  have countLe : count.toNat ≤ len.toNat := by
    have h := UInt64.le_iff_toNat_le.mp within
    rw [UInt64.toNat_div] at h
    have := Nat.div_le_self len.toNat 2
    simpa only [show (2 : UInt64).toNat=2 from rfl] using Nat.le_trans h this
  have countEnd : (reference.offset+count).toNat ≤ (reference.offset+len).toNat := by
    simp only [UInt64.toNat_add,Nat.mod_eq_of_lt sumFits,Nat.mod_eq_of_lt (show reference.offset.toNat+count.toNat<2^64 by omega)]
    omega
  have sourceInitialized := S02SameDestinationAcceptedResultJoin.initialized_subrange sourceEntry.allocation.initializationMask
    (Size.ofBytes reference.offset) (Size.ofBytes (reference.offset+len)) (Size.ofBytes (reference.offset+count)) initialized countEnd
  let buffer : LocalAllocation Provenance BorrowTree MiriMemoryKind := {sourceEntry with allocation := sourceEntry.allocation.setExtra guardTree}
  have valid1 : 1 < guard.locals.size := by rw [sizeAfter];decide
  have valid15 : 15 < guard.locals.size := by rw [sizeAfter];decide
  have valid16 : 16 < guard.locals.size := by rw [sizeAfter];decide
  have guardSource : guard.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue (config options (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete reference.id mutableRaw.parentTag) (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm) := by
    have old := congrArg LocalState.value (Option.some.inj ((Array.getElem?_eq_getElem valid1).symm.trans (sourceAfter.trans sourceCell)))
    simpa only [mutableRaw,rawTag,sourceTag,CanonicalConfigFacts.actual_access_runtime] using old
  have guardSourceCache : guard.locals[1].layout = some ActualReferenceMetadata.reference :=
    congrArg LocalState.layout (Option.some.inj ((Array.getElem?_eq_getElem valid1).symm.trans (sourceAfter.trans sourceCell)))
  have guardCell15 := Option.some.inj ((Array.getElem?_eq_getElem valid15).symm.trans slot15After)
  have guardCell16 := Option.some.inj ((Array.getElem?_eq_getElem valid16).symm.trans slot16After)
  have guardTrack : guard.trackCallerArg = none := by rw [trackAfter,shape.track,frameLiteral];rfl
  have relevant : guard.extra.userRelevance > 0 := by
    rw [extraAfter,shape.extra,frameLiteral,PositiveRootInstalledFrame.relevance,PositiveRootInstalledFrame.raw_relevance]
    decide
  have guardClocks : guard.extra.dataRace = none := by rw [extraAfter];exact noClocks
  have guardMode : held.retagMode = .Default := modeAfter.trans mode
  have high : ∀ index,17≤index→index≤24→guard.locals[index]?=some ⟨.dead,none⟩ := by
    intro index lo hi
    rw [highAfter index lo,shape.keep index (by omega),frameLiteral]
    simpa only [show ¬(14=index ∨ 13=index ∨ 6=index ∨ 0=index) from by omega,
      show 2≠index from by omega,show 1≠index from by omega,ite_false] using slots ⟨index,by omega⟩
  have guardSlot2 : guard.locals[2]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ := by
    rw [countAfter,shape.slot2,frameLiteral];exact slots ⟨2,by decide⟩
  have guardSlot0 : guard.locals[0]?=some ⟨.live (.immediate .uninit),none⟩ := zeroAfter.trans slot0
  have limitPositive : 0 < limits.validation := by have h:=input.contract.resources.executionFuel.2.2.2;unfold work at h;omega
  obtain ⟨ctx⟩ := ActualReferenceContext.exists_context options remaining span input.contract.model.preciseOff input.contract.model.implicitOff
  obtain ⟨copyPacket,copied,done,finalMachine,protectedEq,counterGrowth,sourceMetadata,copyTrace,ready,
    copyMemory,copyLive,copySize,copyLen,copyRuntime,copyPositive,copyActivity,copyTracked,copyAddresses,copyExtras,
    copyBackend,copyGhost,copyShallow,copyRace,copyFixed,copyUnchecked,copyNoGc,connection,physical,copyThread⟩ :=
    S02SameDestinationAcceptedSourceLedger.invoke options limits remaining span ctx input.contract.model.debugOff input.contract.model.nullComparator
      (options.place.dynamicFuel-1) (options.limits.validation-1) (Nat.sub_add_cancel dynamicPositive).symm (Nat.sub_add_cancel validationPositive).symm
      reference.id buffer reference.base reference.offset len raw.parentTag positive nonzero signedFits bounds guard post held trackedAfter guardMode
      mutableRaw.tagRoom runtimeAfter mutableRaw rfl rfl rfl guardCapacity valid15 (congrArg LocalState.value guardCell15) (congrArg LocalState.layout guardCell15)
      guardClocks ghostAfter shallowAfter guardCached guardLive raceAfter guardMetadata guardNotConstructed finalThread finalActive headroom tagsRoom
      input.contract.model.preciseOff input.contract.model.implicitOff (DuplicatePrefixCallModel.sourceComparator options remaining span before input.contract.model)
      (limits.callDispatch-1) (Nat.sub_add_cancel dispatchPositive).symm backendAfter uncheckedAfter noGcAfter fixedAfter finalTop sizeAfter
      (bodyAfter.trans body) (identityAfter.trans identity) (calleeAfter.trans callee) guardTrack relevant allAfter locationAfter
      valid16 (congrArg LocalState.value guardCell16) (congrArg LocalState.layout guardCell16) valid1 guardSource guardSourceCache count countPositive within
      guardSlot2 flagAfter high raw.parent activityAfter guardSlot0 (limits.validation-1) (Nat.sub_add_cancel limitPositive).symm
      storage maskValid sourceMaskLen sourceInitialized currentDirect storageFits mutable sourceExtras
      (CanonicalCopyBound.guarded options () (remaining+1) span len count within)
  obtain ⟨guardReturnActivity,guardReturnNode,guardReturnPresent,guardReturnSame,guardReturnEdge,guardReturnLeaf,guardReturnHidden⟩ :=
    S02SameDestinationRejectedResultLiteralActivity.preserves sourceEntry.allocation.extra tracker reference.id packet.sourceRuntime raw nodes nodeRoom tagRoom
      packet.child packet.returnNode packet.returnPresent packet.returnLeaf packet.returnHidden (by rw [rawParent];exact packet.childrenDifferent)
      packet.destination.offset (packet.destination.offset+1) packet.activity
  rw [←literalEq] at guardReturnActivity guardReturnPresent
  have guardReturnTagged : guardTree.indexOfTag packet.returnTag = some packet.child := by
    obtain ⟨node,present,tagEq,parentEq,hiddenEq,tagged⟩ := graphAfter.oldNodes packet.child packet.returnNode packet.returnPresent
    rw [←packet.returnSame];exact tagged
  have guardParentTagged : guardTree.indexOfTag packet.destination.tag = some packet.destination.parent := by
    rw [literalEq]
    exact S02SameDestinationRejectedResultLookup.literal sourceEntry.allocation.extra tracker reference.id packet.sourceRuntime raw nodes nodeRoom tagRoom
      packet.destination.tag packet.destination.parent packet.destination.tagged
  have disjoint : raw.offset.toNat+raw.len.toNat ≤ packet.destination.offset.toNat ∨ (packet.destination.offset+1).toNat ≤ raw.offset.toNat := by
    have stop : (packet.sourceOffset+packet.sourceLen).toNat = packet.sourceOffset.toNat+packet.sourceLen.toNat := by
      rw [UInt64.toNat_add,Nat.mod_eq_of_lt];exact Nat.lt_of_le_of_lt packet.sourcePositive.bounds packet.destination.entry.allocation.extra.locations.size.bytes.toNat_lt
    have h := packet.disjoint
    rw [stop] at h
    simpa only [rawOffset,rawLen,sourceOffset,sourceLen] using h
  obtain ⟨guardReturnPositive⟩ := S02DisjointSharedLenLiteral.destination sourceEntry.allocation.extra tracker reference.id packet.sourceRuntime raw nodes nodeRoom tagRoom
    (some packet.child) (some packet.selected) packet.maximum packet.destination.offset 1 disjoint packet.positive
  rw [←literalEq,←graphAfter.protections] at guardReturnPositive
  have different : packet.child ≠ raw.parent := by rw [rawParent];exact packet.childrenDifferent
  obtain ⟨⟨returnPositive⟩,returnActivity,⟨returnNode,returnPresent,returnSame,returnEdge,returnLeaf,returnHidden⟩,currentOrder,currentTags,currentCapacity⟩ :=
    S02SameDestinationAcceptedCopyDestination.current buffer post reference.id reference.base reference.offset len count held runtimeAfter mutableRaw
      headroom tagsRoom guardOrder copyPacket copied connection packet.child packet.selected packet.maximum packet.destination.offset 1
      (by simpa only [mutableRaw,rawOffset,rawLen] using disjoint) guardReturnPositive
      guardReturnNode guardReturnPresent guardReturnLeaf guardReturnHidden different guardReturnActivity
  have finalAddresses : finalMachine.user.addresses = machine.user.addresses := by rw [copyAddresses,addressesAfter];exact tickAddresses
  have finalLive : finalMachine.memory.live.find? (fun row => row.1 == packet.destination.id) = some (packet.destination.id,⟨packet.destination.entry.kind,copied⟩) := by rw [sourceId];exact copyLive
  let destination := S02SameDestinationAcceptedResultJoin.destination packet.destination copied finalLive finalAddresses copySize copyLen physical
    (currentCapacity.trans graphAfter.capacity) (currentTags packet.destination.tag packet.destination.parent guardParentTagged)
  obtain ⟨sourceNode,sourceNodePresent,sourceNodeTag,sourceNodeExposure⟩ := sourceMetadata.oldNode oldNode sourcePresent
  have copiedHidden : sourceNode.isExposed = false := sourceNodeExposure.trans sourceHidden
  have copiedTagged : copied.extra.indexOfTag raw.parentTag = some raw.parent := by
    apply sourceMetadata.tagged oldNode sourcePresent
    exact (oldTag.trans sourceSame).trans rawTag.symm
  have sourceOwned : packet.borrowFrame.protectedTags = #[(destination.id,raw.parentTag),(destination.id,packet.returnTag)] := by
    change packet.borrowFrame.protectedTags = #[(packet.destination.id,raw.parentTag),(packet.destination.id,packet.returnTag)]
    simpa only [rawTag] using packet.owned
  have currentReturnTagged := currentTags packet.returnTag packet.child guardReturnTagged
  have hiddenFrame := S02SameDestinationHiddenFrame.of_hidden copied.extra (GeneralBorrowRawAsMutToCopy.held copyPacket).global packet.borrowFrame
    destination.id destination.id raw.parentTag packet.returnTag packet.child returnNode sourceOwned copyRuntime raw.parent sourceNode
    copiedTagged sourceNodePresent copiedHidden currentReturnTagged returnPresent returnHidden
  obtain ⟨sourcePositive⟩ := copyPositive
  have afterSourceActivity := S02HiddenLeafActiveRelease.release copied.extra (GeneralBorrowRawAsMutToCopy.held copyPacket).global copyRuntime raw.parentTag
    raw.parent copyPacket.selected copyPacket.maximum reference.offset len sourcePositive sourceNode sourceNodePresent copiedHidden copiedTagged
    sourceMetadata.distinct (fun _ _ => currentOrder) sourceMetadata.short copyActivity packet.child returnNode returnPresent returnLeaf returnHidden
    different destination.offset (destination.offset+1) returnActivity
  have frameTracked : done.extra.borrowTracker = some packet.borrowFrame := by rw [ready.extra,extraAfter,shape.extra];exact packet.frameTracked
  have donePlace : done.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩ := by
    rw [ready.destination,placeAfter,shape.returnPlace,frameLiteral,frameMetadata.2.2.2.2.1];rfl
  have doneClocks : done.extra.dataRace = none := by rw [ready.extra];exact guardClocks
  have valid0 : (0 : MIR.LocalId) < done.locals.size := by rw [ready.size];decide
  have cell0 := Option.some.inj ((Array.getElem?_eq_getElem valid0).symm.trans ready.output)
  have finalExtras : finalMachine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == destination.id) = some (destination.id,⟨none,#[]⟩) := by
    change finalMachine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == packet.destination.id) = some (packet.destination.id,⟨none,#[]⟩)
    rw [copyExtras,sourceId];exact sourceExtras
  let copyActiveThread := Classical.choose copyThread
  have copyActive : finalMachine.threads.activeThread? = some copyActiveThread := Classical.choose_spec copyThread
  obtain ⟨updated,returnStep,_,_,_⟩ := S03ActiveSameReturnStepBounds.step options limits remaining span done finalMachine
    (GeneralBorrowRawAsMutToCopy.held copyPacket) packet.borrowFrame copyTracked frameTracked place destination raw.parentTag raw.parent
    copyPacket.selected copyPacket.maximum reference.offset len sourceNode copiedTagged sourceNodePresent copiedHidden copyRuntime sourcePositive
    sourceMetadata.distinct (fun _ _ => currentOrder) sourceMetadata.short copyActivity packet.returnTag packet.child packet.selected packet.maximum returnNode
    currentReturnTagged returnPresent (returnSame.trans (guardReturnSame.trans packet.returnSame))
    (returnEdge.trans (guardReturnEdge.trans packet.returnEdge)) returnHidden sourceOwned hiddenFrame copyRuntime returnPositive
    sourceMetadata.distinct (fun _ _ => currentOrder) sourceMetadata.short
    (by change (reference.offset+len).toNat ≤ packet.destination.offset.toNat ∨ (packet.destination.offset+1).toNat ≤ reference.offset.toNat
        simpa only [sourceOffset,sourceLen] using packet.disjoint) afterSourceActivity copyActiveThread copyActive copyRace copyBackend copyGhost copyShallow
    #[] finalExtras (by simp) true (options.limits.validation-1) input.contract.model.debugOff (Nat.sub_add_cancel validationPositive).symm
    (ready.body.trans (bodyAfter.trans body)) ready.location valid0 (congrArg LocalState.value cell0) (congrArg LocalState.layout cell0) doneClocks donePlace
    (by rw [ready.continuation,continuationAfter,shape.continuation,frameLiteral];exact frameMetadata.2.2.2.1) ready.immediate
    (by rw [ready.varargs,varargsAfter,shape.vaList,frameLiteral,frameMetadata.2.2.2.2.2.1];rfl) copyUnchecked copyNoGc copyFixed
  let accounted := S04FinalReturnRuleAccounting.machine options remaining span done finalMachine
  let sourceReleased := (copied.extra.releaseProtector raw.parentTag (GeneralBorrowRawAsMutToCopy.held copyPacket).global.protectedTags).tree
  let priorMemory := StackPopRelease.commitTree accounted.memory destination.id destination.entry sourceReleased
  let released := (sourceReleased.releaseProtector packet.returnTag (GeneralBorrowRawAsMutToCopy.held copyPacket).global.protectedTags).tree
  let after := S04FinalReturnVariantsInput.afterPop #[] done accounted (GeneralBorrowRawAsMutToCopy.held copyPacket) packet.borrowFrame
    priorMemory destination.id destination.entry released (copyActiveThread.topUserRelevantFrame.getD 0)
  let finished := CanonicalCopy.replaceAllocation after destination.id destination.entry.kind updated
  have last : ExecutionMachine.step (config options (remaining+1) span) limits () (Storage.withCurrent #[] done finalMachine) = (finished,.ok true) := returnStep
  have trace := SuccessfulTrace.append (SuccessfulTrace.append prefixTrace acceptedTrace) (SuccessfulTrace.append copyTrace (.next last (.refl _)))
  let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit := ⟨config options (remaining+1) span,limits,fun _ _ => True⟩
  have entered : CallSafety.IsCallEntry 1 (Storage.withCurrent #[] entry machine) := by simp [CallSafety.IsCallEntry,CallSafety.frameDepth,Storage.withCurrent]
  have exited : CallSafety.pastCallBoundary 1 finished := by change (0:Nat)<1;decide
  have terminal : ExecutionMachine.step (config options (remaining+1) span) limits () finished = (finished,.ok false) := rfl
  exact ⟨Storage.withCurrent #[] entry machine,finished,actual,trace,terminal,rfl,
    SuccessfulTrace.no_errors safety 1 _ _ entered trace exited,SuccessfulTrace.no_ub safety 1 _ _ entered trace exited,
    SuccessfulTraceTerminal.prefix_step_success trace terminal⟩
/-- Fix the original positive witness, removing dependence on existential choice. -/
theorem same_id
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before} {place : MPlaceTy Provenance}
    (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance = .concrete input.contract.destination.id returnTag)
    (countPositive : (0 : UInt64) < count) (within : count ≤ len/2)
    (reference : DuplicatePrefixReferenceInput.Positive before (Pointer.new .wildcard (Size.ofBytes address)) len)
    (same : reference.id = input.contract.destination.id) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len count place := by
  obtain ⟨resolved,run⟩ := result address len count input nonempty returnTag returnConcrete countPositive within
  have unique := S02WildcardPositiveIdUnique.same_id address len reference resolved
  exact run (by rw [←unique];exact same)
end
end DuplicatePrefix.S02WildcardSameDestinationAcceptedResult
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardSameDestinationAcceptedResult.result) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved wildcard same accepted Result dependency {dependency}"
