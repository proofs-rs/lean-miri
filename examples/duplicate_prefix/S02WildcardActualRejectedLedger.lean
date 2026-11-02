import duplicate_prefix.S02WildcardRejectedEntryPrefixCapacity
import duplicate_prefix.S02WildcardRejectedSiteFrame
import duplicate_prefix.S02WildcardRejectedSiteSlots
import duplicate_prefix.GeneralBorrowRawSharedToRejectedLedger
import duplicate_prefix.S02SeparateDestinationTickLedger

namespace DuplicatePrefix.S02WildcardActualRejectedLedger
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The actual positive wildcard call executes shared Ref, slice::len and
its rejected false-store branch on the exact installed source/destination packet. -/
theorem executes_rejected_ledger
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag)
    (rejected : count > len/2) :
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
      result.location = .mir ⟨10,0⟩ ∧
      result.locals[0]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ ∧
      result.body = frame.body ∧ result.bodyIdentity = frame.bodyIdentity ∧
      result.functionInstance = frame.functionInstance ∧ result.extra = frame.extra ∧
      result.returnPlace = frame.returnPlace ∧ result.returnContinuation = frame.returnContinuation ∧
      result.vaList = frame.vaList ∧ result.localsIdentity = frame.localsIdentity ∧
      result.locals.size = 25 ∧ CopyHelperCleanup.AllImmediate result ∧
      post.memory = RetagEntry.updatedMemory
        (RootZeroCompleteState.tick options remaining span machine).memory reference.id
        packet.sourceEntry finalTree ∧
      post.borrowTracker = some held ∧ held.retagMode = packet.tracker.retagMode ∧
      DuplicatePrefixBorrowContract.RuntimeFacts finalTree held.global ∧
      Nonempty (GeneralBorrowReadRowRange.Positive finalTree held.global.protectedTags child
        raw.selected raw.maximum reference.offset len) ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive finalTree held.global.protectedTags
        (some raw.parent) (some raw.selected) raw.maximum reference.offset len) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin finalTree raw.parent .Write
        reference.offset (reference.offset+len) ∧
      GeneralBorrowRawSharedToLenLedger.Graph packet.sourceEntry.allocation.extra finalTree
        raw.selected packet.tracker held := by
  obtain ⟨reference,ready⟩ :=
    S02WildcardRejectedEntryPrefixCapacity.executes address len count input nonempty rejected
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
  have shortRoom : sourceEntry.allocation.extra.nodes.size+2 < 65536 := nodes
  have nodeRoom : sourceEntry.allocation.extra.nodes.size+2 ≤ 4294967295 := by omega
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
  obtain ⟨slot0,slot13,slot7,slot8,slot9,slot10⟩ :=
    S02WildcardRejectedSiteSlots.from_shape address len count input reference
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
  have cell (n : Fin 25) : n.val < frame.locals.size := by rw [size]; exact n.isLt
  have fromSlot (n : Fin 25) (value : LocalState Provenance LocalLayout)
      (h : frame.locals[n.val]? = some value) : frame.locals[n.val]'(cell n) = value :=
    Option.some.inj ((Array.getElem?_eq_getElem (cell n)).symm.trans h)
  obtain ⟨result,post,tree,held,child,bodyTrace,loc,_size2,_body2,_ident2,_calle2,_extra2,
    _place2,_cont2,_va2,_localid2,slotFalse,_imm2,_mem2,_borrow2,_mode2,_runtime2,_positive2,bothAfter,activityAfter,graphAfter⟩ :=
    GeneralBorrowRawSharedToRejectedLedger.complete options limits remaining span
      input.contract.model.preciseOff input.contract.model.implicitOff input.contract.model.debugOff
      input.contract.model.nullComparator (options.place.dynamicFuel-1) (options.limits.validation-1)
      (Nat.sub_add_cancel dynamicPositive).symm (Nat.sub_add_cancel validationPositive).symm
      reference.base reference.offset len reference.id sourceEntry positive nonzero signedFits #[] frame current
      body identity callee located tracker enabled mode fresh reference.tracker.global.nextPointerTag
      packet.sourceRuntime raw rawTag rawOffset rawLen capacity validSource validDest sourceLive sourceCached
      destLive destUncached noClocks' ghost shallow cached present race metadata notConstructed
      shortRoom nodeRoom tagRoom rfl (limits.callDispatch-1) (Nat.sub_add_cancel dispatchPositive).symm
      (DuplicatePrefixCallModel.sourceComparator options remaining span before input.contract.model)
      valid11 lenLive lenUncached backend unchecked noGc fixed
      {input.contract.thread with topUserRelevantFrame := some 0} active topZero
      count rejected size
      (congrArg LocalState.value (fromSlot ⟨13,by decide⟩ _ slot13))
      (congrArg LocalState.layout (fromSlot ⟨13,by decide⟩ _ slot13))
      (congrArg LocalState.value (fromSlot ⟨0,by decide⟩ _ slot0))
      (congrArg LocalState.layout (fromSlot ⟨0,by decide⟩ _ slot0))
      (congrArg LocalState.value (fromSlot ⟨7,by decide⟩ _ slot7))
      (congrArg LocalState.value (fromSlot ⟨8,by decide⟩ _ slot8))
      (congrArg LocalState.layout (fromSlot ⟨8,by decide⟩ _ slot8))
      (congrArg LocalState.value (fromSlot ⟨9,by decide⟩ _ slot9))
      (congrArg LocalState.layout (fromSlot ⟨9,by decide⟩ _ slot9))
      (congrArg LocalState.value (fromSlot ⟨10,by decide⟩ _ slot10))
      (congrArg LocalState.layout (fromSlot ⟨10,by decide⟩ _ slot10)) immediate bothRaw activityRaw
  exact ⟨entry,frame,result,machine,post,packet,raw,tree,held,child,
    actual,prefixTrace,bodyTrace,loc,slotFalse,_body2,_ident2,_calle2,_extra2,_place2,
    _cont2,_va2,_localid2,_size2,_imm2,_mem2,_borrow2,_mode2,_runtime2,_positive2,
    bothAfter,activityAfter,graphAfter⟩

end
end DuplicatePrefix.S02WildcardActualRejectedLedger

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardActualRejectedLedger.executes_rejected_ledger) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard actual rejected ledger dependency {dependency}"
