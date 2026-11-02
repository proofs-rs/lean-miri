import duplicate_prefix.S02SeparateDestinationPacketSourceTag
import duplicate_prefix.S02WildcardAcceptedEntryPrefixMargin
import duplicate_prefix.S02WildcardAcceptedSiteSlots
import duplicate_prefix.S02WildcardRejectedSiteFrame
import duplicate_prefix.S02SeparateDestinationTickLedger
import duplicate_prefix.GeneralBorrowRawSharedToAcceptedLedgerRuntimeSlot0

namespace DuplicatePrefix.S02WildcardAcceptedSharedLedgerMargin
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Actual positive wildcard call reaches the accepted guard after real shared Ref and len. -/
theorem executes
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (countPositive : 0 < count.toNat) (within : count ≤ len/2)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new .wildcard (Size.ofBytes address)) len),
      reference.id ≠ input.contract.destination.id →
    ∃ (entry frame result : CompilerFrameContext.ActualFrame)
      (machine post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (packet : S02SeparateDestinationZeroCore.Packet entry machine place)
      (raw : GeneralBorrowRawShared.Input packet.sourceEntry.allocation.extra packet.tracker.global)
      (finalTree : BorrowTree) (held : MachineHooks.BorrowState) (child : UniIndex),
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] entry machine) ∧
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] entry machine)
        (Storage.withCurrent #[] frame (RootZeroCompleteState.tick options remaining span machine)) ∧
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] frame (RootZeroCompleteState.tick options remaining span machine))
        (Storage.withCurrent #[] result post) ∧
      result.location = .mir ⟨6,7⟩ ∧ result.locals.size = 25 ∧
      result.body = RootBody.reflected.body.body ∧ result.bodyIdentity = RootBody.reflected.body.identity ∧
      result.functionInstance = RootBody.reflected.functionInstance ∧
      result.extra = entry.extra ∧ result.returnPlace = entry.returnPlace ∧
      result.returnContinuation = entry.returnContinuation ∧ result.vaList = entry.vaList ∧
      result.localsIdentity = frame.localsIdentity ∧ result.trackCallerArg = frame.trackCallerArg ∧
      result.locals[0]? = frame.locals[0]? ∧ result.locals[1]? = frame.locals[1]? ∧
      result.locals[2]? = frame.locals[2]? ∧
      result.locals[13]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ ∧
      result.locals[15]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[16]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      (∀ index, 17 ≤ index → result.locals[index]? = frame.locals[index]?) ∧
      CopyHelperCleanup.AllImmediate result ∧
      post.memory = RetagEntry.updatedMemory (RootZeroCompleteState.tick options remaining span machine).memory
        reference.id packet.sourceEntry finalTree ∧
      post.borrowTracker = some held ∧ held.retagMode = packet.tracker.retagMode ∧
      DuplicatePrefixBorrowContract.RuntimeFacts finalTree held.global ∧
      Nonempty (GeneralBorrowReadRowRange.Positive finalTree held.global.protectedTags child
        raw.selected raw.maximum reference.offset len) ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive finalTree held.global.protectedTags
        (some raw.parent) (some raw.selected) raw.maximum reference.offset len) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin finalTree raw.parent .Write
        reference.offset (reference.offset+len) ∧
      GeneralBorrowRawSharedToLenLedger.Graph packet.sourceEntry.allocation.extra finalTree
        raw.selected packet.tracker held ∧
      post.user.payload.ghost = false ∧ post.user.payload.validation = .Shallow ∧ post.dataRace = none ∧
      post.user.addresses = (RootZeroCompleteState.tick options remaining span machine).user.addresses ∧
      post.user.payload.payload.user.types = (RootZeroCompleteState.tick options remaining span machine).user.payload.payload.user.types ∧
      post.user.payload.payload.user.runtime.extras = (RootZeroCompleteState.tick options remaining span machine).user.payload.payload.user.runtime.extras ∧
      post.user.payload.payload.user.backend = .none ∧
      ((config options (remaining+1) span).terminators.getControl post.user).checkedArithmetic = false ∧
      ((config options (remaining+1) span).terminators.getControl post.user).gcInterval = 0 ∧
      post.threads.fixedScheduling = true ∧
      (∃ nextThread, post.threads.activeThread? = some nextThread ∧ nextThread.topUserRelevantFrame = some 0) ∧
      packet.sourceId = reference.id ∧ packet.sourceTag = raw.parentTag ∧
      raw.parent = packet.sourceChild ∧ raw.selected = packet.sourceChild ∧
      packet.sourceSelected = packet.sourceChild ∧ raw.maximum = packet.sourceMaximum ∧
      packet.sourceOffset = reference.offset ∧ packet.sourceLen = len ∧
      packet.sourceNode.tag = packet.sourceTag ∧
      entry = PositiveRootInstalledFrame.installed
        (RawRootInvocation.root before place input.contract.model.noDataRace)
        (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
            (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
        count {} reference.id reference.tracker.global.nextPointerTag
        packet.destination.id packet.returnTag ∧
      packet.sourceEntry.allocation.extra.nodes.size+4 < 65536 ∧
      packet.tracker.global.nextPointerTag.value.toNat+3 < 18446744073709551615 := by
  obtain ⟨reference,ready⟩ :=
    S02WildcardAcceptedEntryPrefixMargin.executes address len count input nonempty countPositive
      returnTag returnConcrete
  refine ⟨reference,?_⟩
  intro different
  obtain ⟨entry,machine,packet,raw,frame,actual,rawTag,rawParent,rawOffset,rawLen,
    sourceId,rawSelected,rawMaximum,sourceTag,sourceSelected,sourceMaximum,sourceOffset,sourceLen,
    frameLiteral,rawUser,rawThreads,rawRace,mode,prefixTrace,shape,
    capacity,bounds,nodes,tagRoom⟩ := ready different
  let tracker := packet.tracker
  let sourceEntry := packet.sourceEntry
  let current := RootZeroCompleteState.tick options remaining span machine
  obtain ⟨tickMemory,tickTracker,tickRace,tickThreads,tickAddresses,tickTypes,tickBackend,tickExtras⟩ :=
    S02SeparateDestinationTickLedger.preserved options remaining span machine
  have enabled : current.borrowTracker = some tracker := by
    rw [tickTracker]; exact packet.enabled
  have present : current.memory.live.find? (fun row => row.1 == reference.id) =
      some (reference.id,sourceEntry) := by
    rw [tickMemory,←sourceId]; exact packet.sourceLive
  obtain ⟨_rawMemory,_rawBorrow,rawRace0,rawAddresses,rawGhost,rawShallow,rawTypes,
    rawBackend,_rawExtras⟩ := RawRootInvocation.preservation #[] before
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
  have shortRoom : sourceEntry.allocation.extra.nodes.size+2 < 65536 := by
    change packet.sourceEntry.allocation.extra.nodes.size+2 < 65536
    omega
  have nodeRoom : sourceEntry.allocation.extra.nodes.size+2 ≤ 4294967295 := by omega
  have smallTagRoom : tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615 := by
    change packet.tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615
    omega
  have dynamicPositive : 0 < options.place.dynamicFuel := by
    have h := input.contract.resources.dynamicFuel
    unfold work at h
    omega
  have validationPositive : 0 < options.limits.validation := by
    have h := input.contract.resources.configuredFuel.2.2.2
    unfold work at h
    omega
  have dispatchPositive : 0 < limits.callDispatch := by
    have h := input.contract.resources.executionFuel.1
    unfold work at h
    omega
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
  have topZero : ({input.contract.thread with topUserRelevantFrame := some 0}).topUserRelevantFrame = some 0 := rfl
  have bothRaw : DuplicatePrefixBorrowAuthorization.Positive sourceEntry.allocation.extra
      tracker.global.protectedTags (some raw.parent) (some raw.selected) raw.maximum reference.offset len := by
    simpa only [rawParent,rawSelected,rawMaximum,sourceSelected,sourceMaximum,sourceOffset,sourceLen] using packet.sourcePositive
  have activityRaw : GeneralBorrowFreshActiveWithin.ActiveWithin sourceEntry.allocation.extra
      raw.parent .Write reference.offset (reference.offset+len) := by
    rw [rawParent,←sourceOffset,←sourceLen]
    exact packet.sourceActivity
  have siteCell (i : Nat) (valid : i < frame.locals.size)
      (row : LocalState Provenance LocalLayout) (present : frame.locals[i]? = some row) :
      frame.locals[i] = row :=
    Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans present)
  have countPositive64 : (0 : UInt64) < count := UInt64.lt_iff_toNat_lt.mpr countPositive
  obtain ⟨result,post,finalTree,held,child,acceptedTrace,locationAfter,sizeAfter,bodyAfter,identityAfter,
    calleeAfter,extraAfter,placeAfter,continuationAfter,varargsAfter,localsIdentityAfter,trackAfter,
    zeroAfter,sourceAfter,countAfter,flagAfter,slot15After,slot16After,highAfter,allAfter,
    memoryAfter,trackedAfter,modeAfter,runtimeAfter,readAfter,bothAfter,activityAfter,graphAfter,
    ghostAfter,shallowAfter,raceAfter,addressesAfter,typesAfter,extrasAfter,backendAfter,uncheckedAfter,noGcAfter,
    fixedAfter,threadAfter⟩ :=
    GeneralBorrowRawSharedToAcceptedLedgerRuntimeSlot0.complete options limits remaining span
      input.contract.model.preciseOff input.contract.model.implicitOff input.contract.model.debugOff
      input.contract.model.nullComparator (options.place.dynamicFuel-1) (options.limits.validation-1)
      (Nat.sub_add_cancel dynamicPositive).symm (Nat.sub_add_cancel validationPositive).symm
      reference.base reference.offset len reference.id sourceEntry positive nonzero signedFits #[] frame current
      body identity callee located tracker enabled mode fresh reference.tracker.global.nextPointerTag
      packet.sourceRuntime raw rawTag rawOffset rawLen capacity validSource validDest sourceLive sourceCached
      destLive destUncached noClocks ghost shallow cached present race metadata notConstructed
      shortRoom nodeRoom smallTagRoom rfl (limits.callDispatch-1) (Nat.sub_add_cancel dispatchPositive).symm
      (DuplicatePrefixCallModel.sourceComparator options remaining span before input.contract.model)
      valid11 lenLive lenUncached backend unchecked noGc fixed
      {input.contract.thread with topUserRelevantFrame := some 0} active topZero
      count countPositive64 within size
      (congrArg LocalState.value (siteCell 13 (by rw [size]; decide) _ slot13))
      (congrArg LocalState.layout (siteCell 13 (by rw [size]; decide) _ slot13))
      (congrArg LocalState.value (siteCell 0 (by rw [size]; decide) _ slot0))
      (congrArg LocalState.layout (siteCell 0 (by rw [size]; decide) _ slot0))
      (congrArg LocalState.value (siteCell 7 (by rw [size]; decide) _ slot7))
      (congrArg LocalState.layout (siteCell 7 (by rw [size]; decide) _ slot7))
      (congrArg LocalState.value (siteCell 15 (by rw [size]; decide) _ slot15))
      (congrArg LocalState.layout (siteCell 15 (by rw [size]; decide) _ slot15))
      (congrArg LocalState.value (siteCell 16 (by rw [size]; decide) _ slot16))
      (congrArg LocalState.layout (siteCell 16 (by rw [size]; decide) _ slot16))
      (congrArg LocalState.value (siteCell 8 (by rw [size]; decide) _ slot8))
      (congrArg LocalState.layout (siteCell 8 (by rw [size]; decide) _ slot8))
      (congrArg LocalState.value (siteCell 9 (by rw [size]; decide) _ slot9))
      (congrArg LocalState.layout (siteCell 9 (by rw [size]; decide) _ slot9))
      (congrArg LocalState.value (siteCell 10 (by rw [size]; decide) _ slot10))
      (congrArg LocalState.layout (siteCell 10 (by rw [size]; decide) _ slot10))
      immediate bothRaw activityRaw
  exact ⟨entry,frame,result,machine,post,packet,raw,finalTree,held,child,
    actual,prefixTrace,acceptedTrace,locationAfter,sizeAfter,bodyAfter.trans body,
    identityAfter.trans identity,calleeAfter.trans callee,
    extraAfter.trans shape.extra,placeAfter.trans shape.returnPlace,
    continuationAfter.trans shape.continuation,varargsAfter.trans shape.vaList,
    localsIdentityAfter,trackAfter,zeroAfter,sourceAfter,countAfter,flagAfter,slot15After,slot16After,
    highAfter,allAfter,memoryAfter,trackedAfter,modeAfter,runtimeAfter,readAfter,bothAfter,
    activityAfter,graphAfter,ghostAfter,shallowAfter,raceAfter,addressesAfter,typesAfter,extrasAfter,
    backendAfter,uncheckedAfter,noGcAfter,fixedAfter,threadAfter,
    sourceId,sourceTag.trans rawTag.symm,rawParent,rawSelected,sourceSelected,
    rawMaximum.trans sourceMaximum.symm,sourceOffset,sourceLen,
    S02SeparateDestinationPacketSourceTag.same packet sourceSelected
      (sourceMaximum.trans (congrArg some sourceTag.symm)),frameLiteral,nodes,tagRoom⟩

end
end DuplicatePrefix.S02WildcardAcceptedSharedLedgerMargin

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardAcceptedSharedLedgerMargin.executes) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard accepted shared ledger dependency {dependency}"
