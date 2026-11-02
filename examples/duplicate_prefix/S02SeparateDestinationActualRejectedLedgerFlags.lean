import duplicate_prefix.S02SeparateDestinationSharedFullSite
import duplicate_prefix.S02SeparateDestinationSharedSiteBounds
import duplicate_prefix.S02SeparateDestinationSharedSiteGeometry
import duplicate_prefix.GeneralBorrowRawSharedToRejectedLedgerState
import duplicate_prefix.S02SeparateDestinationRejectedBothShapeSite
import duplicate_prefix.S02SeparateDestinationSharedShapeSite
import duplicate_prefix.S02SeparateDestinationRejectedSiteSlots

namespace DuplicatePrefix.S02SeparateDestinationActualRejectedLedgerFlags
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The actual positive rejected call reaches and executes shared Ref and slice::len. -/
theorem executes_rejected_ledger_flags
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (different : id ≠ input.contract.destination.id)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag)
    (rejected : count > len/2) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
      (tracker : MachineHooks.BorrowState)
      (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
      (raw : GeneralBorrowRawShared.Input sourceEntry.allocation.extra tracker.global)
      (entry frame result : CompilerFrameContext.ActualFrame)
      (machine post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (finalTree : BorrowTree) (held : MachineHooks.BorrowState) (child : UniIndex),
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] entry machine) ∧
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] entry machine)
        (Storage.withCurrent #[] frame (RootZeroCompleteState.tick options remaining span machine)) ∧
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] frame (RootZeroCompleteState.tick options remaining span machine))
        (Storage.withCurrent #[] result post) ∧ result.location = .mir ⟨10,0⟩ ∧
      result.locals[0]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ ∧
      result.body = frame.body ∧ result.bodyIdentity = frame.bodyIdentity ∧
      result.functionInstance = frame.functionInstance ∧ result.extra = frame.extra ∧
      result.extra = entry.extra ∧
      result.returnPlace = frame.returnPlace ∧ result.returnContinuation = frame.returnContinuation ∧
      result.vaList = frame.vaList ∧ result.localsIdentity = frame.localsIdentity ∧
      result.locals.size = 25 ∧ CopyHelperCleanup.AllImmediate result ∧
      post.memory = RetagEntry.updatedMemory
        (RootZeroCompleteState.tick options remaining span machine).memory reference.id sourceEntry finalTree ∧
      post.borrowTracker = some held ∧ held.retagMode = tracker.retagMode ∧
      DuplicatePrefixBorrowContract.RuntimeFacts finalTree held.global ∧
      Nonempty (GeneralBorrowReadRowRange.Positive finalTree held.global.protectedTags child
        raw.selected raw.maximum reference.offset len) ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive finalTree held.global.protectedTags
        (some raw.parent) (some raw.selected) raw.maximum reference.offset len) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin finalTree raw.parent .Write
        reference.offset (reference.offset+len) ∧
      GeneralBorrowRawSharedToLenLedger.Graph sourceEntry.allocation.extra finalTree raw.selected tracker held ∧
      post.user.addresses = (RootZeroCompleteState.tick options remaining span machine).user.addresses ∧
      post.user.payload.payload.user.types = (RootZeroCompleteState.tick options remaining span machine).user.payload.payload.user.types ∧
      post.user.payload.payload.user.runtime.extras = (RootZeroCompleteState.tick options remaining span machine).user.payload.payload.user.runtime.extras ∧
      post.user.payload.ghost = false ∧ post.user.payload.validation = .Shallow ∧ post.dataRace = none ∧
      post.user.payload.payload.user.backend = .none ∧
      ((config options (remaining+1) span).terminators.getControl post.user).checkedArithmetic = false ∧
      ((config options (remaining+1) span).terminators.getControl post.user).gcInterval = 0 ∧
      post.threads.fixedScheduling = true ∧
      ∃ nextThread, post.threads.activeThread? = some nextThread ∧ nextThread.topUserRelevantFrame = some 0 := by
  obtain ⟨reference,tracker,sourceEntry,child,raw,entry,frame,machine,actual,prefixTrace,
    shape,body,identity,callee,located,size,noClocks,sourceCell,lenCell,exprCell,immediate,
    tracked,live,rawTag,rawParent,rawOffset,rawLen,runtime,⟨both⟩,activity⟩ :=
    S02SeparateDestinationRejectedBothShapeSite.actual_rejected_both_shape_site id tag address len count input
      nonempty different returnTag returnConcrete rejected
  obtain ⟨positive,nonzero,signedFits,_bounds,capacity,shortRoom,nodeRoom,tagRoom⟩ :=
    S02SeparateDestinationSharedSiteBounds.at_actual_call id tag address len count input
      nonempty different returnTag returnConcrete reference tracker sourceEntry entry machine
      actual tracked live
  obtain ⟨addresses,types,backend,ghost,shallow,unchecked,noGc,fixed,race,
    thread,active,topZero⟩ :=
    S02SeparateDestinationSharedSiteGeometry.after_tick id tag address len count input
      nonempty different returnTag returnConcrete entry machine actual
  let current := RootZeroCompleteState.tick options remaining span machine
  obtain ⟨_mem,tickTracker,_race,_threads,_addresses,_types,_backend,_extras⟩ :=
    S02SeparateDestinationTickLedger.preserved options remaining span machine
  have enabled : current.borrowTracker = some tracker := by rw [tickTracker]; exact tracked
  have present : current.memory.live.find? (fun row => row.1 == reference.id) = some (reference.id,sourceEntry) := by
    rw [_mem]; exact live
  have cached : current.user.addresses.baseAddr.find? (fun row => row.allocId == reference.id) = some ⟨reference.id,reference.base⟩ := by
    rw [addresses]; exact reference.cachedBase
  have metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] frame current)).metadata = PreparedReflection.actual.runtime := by
    change current.user.payload.payload.user.types.metadata = _
    rw [types]; exact input.contract.model.metadata
  have notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] frame current)).entries.any (·.value.ty == 4) = false := by
    change current.user.payload.payload.user.types.entries.any (·.value.ty == 4) = _
    rw [types]; exact input.slice_not_constructed
  obtain ⟨_ref2,tracker2,entry2,machine2,actual2,tracked2,mode2,_ghost2,_shallow2,
    _unchecked2,_gc2,_fixed2,_race2⟩ :=
    S02SeparateDestinationMachineSettings.after_exact id tag address len count input nonempty
      different returnTag returnConcrete
  have same2 : Storage.withCurrent #[] entry2 machine2 = Storage.withCurrent #[] entry machine :=
    (EStateM.Result.ok.inj (actual2.symm.trans actual)).2
  have machineEq : machine2 = machine := congrArg (fun s : RootState => s.machine) same2
  have mode : tracker.retagMode = .Default := by
    have trackerEq : tracker2 = tracker := Option.some.inj (by rw [machineEq] at tracked2; exact tracked2.symm.trans tracked)
    rw [←trackerEq]
    exact mode2
  have fresh : tracker.global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    have h : tracker.global.nextPointerTag.value.toNat < 18446744073709551615 := by omega
    simpa using h
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
  have validSource : (1 : MIR.LocalId) < frame.locals.size := by rw [size]; decide
  have validDest : RootReferenceFacts.destination true < frame.locals.size := by rw [size]; decide
  have valid11 : 11 < frame.locals.size := by rw [size]; decide
  have sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
        (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm) := by
    have h := congrArg LocalState.value (Option.some.inj (by simpa [Array.getElem?_eq_getElem validSource] using sourceCell))
    rw [CanonicalConfigFacts.actual_access_runtime options () remaining span,
      CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span] at *
    exact h
  have sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference := by
    exact congrArg LocalState.layout (Option.some.inj (by simpa [Array.getElem?_eq_getElem validSource] using sourceCell))
  have lenLive : frame.locals[11].value = .live (.immediate .uninit) := by
    exact congrArg LocalState.value (Option.some.inj (by simpa [Array.getElem?_eq_getElem valid11] using lenCell))
  have lenUncached : frame.locals[11].layout = none := by
    exact congrArg LocalState.layout (Option.some.inj (by simpa [Array.getElem?_eq_getElem valid11] using lenCell))
  have destCellValid : (12 : MIR.LocalId) < frame.locals.size := by rw [size]; decide
  have destLive : frame.locals[RootReferenceFacts.destination true].value = .live (.immediate .uninit) := by
    have h := congrArg LocalState.value (Option.some.inj (by simpa [Array.getElem?_eq_getElem destCellValid] using exprCell))
    simpa [RootReferenceFacts.destination] using h
  have destUncached : frame.locals[RootReferenceFacts.destination true].layout = none := by
    have h := congrArg LocalState.layout (Option.some.inj (by simpa [Array.getElem?_eq_getElem destCellValid] using exprCell))
    simpa [RootReferenceFacts.destination] using h
  have bothRaw : DuplicatePrefixBorrowAuthorization.Positive sourceEntry.allocation.extra
      tracker.global.protectedTags (some raw.parent) (some raw.selected) raw.maximum reference.offset len := by
    rw [rawParent]
    exact both
  have activityRaw : GeneralBorrowFreshActiveWithin.ActiveWithin sourceEntry.allocation.extra
      raw.parent .Write reference.offset (reference.offset+len) := by
    rw [rawParent]
    exact activity
  obtain ⟨slot0,slot13,slot7,slot8,slot9,slot10⟩ :=
    S02SeparateDestinationRejectedSiteSlots.at_shared_site id tag address len count input
      nonempty different returnTag returnConcrete entry frame machine actual shape
  have cell (n : Fin 25) : n.val < frame.locals.size := by rw [size]; exact n.isLt
  have fromSlot (n : Fin 25) (value : LocalState Provenance LocalLayout)
      (h : frame.locals[n.val]? = some value) : frame.locals[n.val]'(cell n) = value :=
    Option.some.inj ((Array.getElem?_eq_getElem (cell n)).symm.trans h)
  obtain ⟨result,post,tree,held,child,bodyTrace,loc,_size2,_body2,_ident2,_calle2,_extra2,
    _place2,_cont2,_va2,_localid2,slotFalse,_imm2,_mem2,_borrow2,_mode2,_runtime2,_positive2,bothAfter,activityAfter,graphAfter,addressesAfter,typesAfter,extrasAfter,ghostAfter,shallowAfter,raceAfter,backendAfter,
    uncheckedAfter,noGcAfter,fixedAfter,threadAfter⟩ :=
    GeneralBorrowRawSharedToRejectedLedgerState.complete options limits remaining span
      input.contract.model.preciseOff input.contract.model.implicitOff input.contract.model.debugOff
      input.contract.model.nullComparator (options.place.dynamicFuel-1) (options.limits.validation-1)
      (Nat.sub_add_cancel dynamicPositive).symm (Nat.sub_add_cancel validationPositive).symm
      reference.base reference.offset len reference.id sourceEntry positive nonzero signedFits #[] frame current
      body identity callee located tracker enabled mode fresh reference.tracker.global.nextPointerTag
      runtime raw rawTag rawOffset rawLen capacity validSource validDest sourceLive sourceCached
      destLive destUncached noClocks ghost shallow cached present race metadata notConstructed
      shortRoom nodeRoom tagRoom rfl (limits.callDispatch-1) (Nat.sub_add_cancel dispatchPositive).symm
      (DuplicatePrefixCallModel.sourceComparator options remaining span before input.contract.model)
      valid11 lenLive lenUncached backend unchecked noGc fixed thread active topZero
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
  exact ⟨reference,tracker,sourceEntry,raw,entry,frame,result,machine,post,tree,held,child,
    actual,prefixTrace,bodyTrace,loc,slotFalse,_body2,_ident2,_calle2,_extra2,_extra2.trans shape.extra,_place2,
    _cont2,_va2,_localid2,_size2,_imm2,_mem2,_borrow2,_mode2,_runtime2,_positive2,bothAfter,activityAfter,graphAfter,addressesAfter,typesAfter,extrasAfter,ghostAfter,shallowAfter,
    raceAfter,backendAfter,uncheckedAfter,noGcAfter,fixedAfter,threadAfter⟩

end
end DuplicatePrefix.S02SeparateDestinationActualRejectedLedgerFlags

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationActualRejectedLedgerFlags.executes_rejected_ledger_flags) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved actual rejected body dependency {dependency}"
