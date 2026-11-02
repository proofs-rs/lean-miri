import duplicate_prefix.S02ConcreteSourceWildcardSharedInput
import duplicate_prefix.GeneralBorrowRawSharedToLenLedger
import duplicate_prefix.S02SeparateDestinationTickLedger

namespace DuplicatePrefix.S02WildcardGenericSharedLenLedger
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Actual shared Ref/len from an installed positive concrete source site, independent of count branch. -/
theorem complete_at_site
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (different : id ≠ input.contract.destination.id)
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
    (tracker : MachineHooks.BorrowState)
    (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (raw : GeneralBorrowRawShared.Input sourceEntry.allocation.extra tracker.global)
    (entry frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (actual : Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] entry machine))
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (located : frame.location = .mir ⟨2,11⟩)
    (size : frame.locals.size = 25)
    (noClocks : frame.extra.dataRace = none)
    (sourceCell : frame.locals[1]? = some ⟨.live (.immediate
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
          (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm),
      some ActualReferenceMetadata.reference⟩)
    (lenCell : frame.locals[11]? = some ⟨.live (.immediate .uninit),none⟩)
    (exprCell : frame.locals[12]? = some ⟨.live (.immediate .uninit),none⟩)
    (tracked : machine.borrowTracker = some tracker)
    (live : machine.memory.live.find? (fun row => row.1 == reference.id) = some (reference.id,sourceEntry))
    (rawTag : raw.parentTag = reference.tracker.global.nextPointerTag)
    (rawOffset : raw.offset = reference.offset) (rawLen : raw.len = len)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts sourceEntry.allocation.extra tracker.global)
    (both : DuplicatePrefixBorrowAuthorization.Positive sourceEntry.allocation.extra tracker.global.protectedTags
      (some raw.parent) (some raw.selected) raw.maximum reference.offset len)
    (activity : GeneralBorrowFreshActiveWithin.ActiveWithin sourceEntry.allocation.extra raw.parent .Write
      reference.offset (reference.offset+len))
    (bounds : (0 : UInt64) < len ∧ reference.base+reference.offset ≠ 0 ∧
      len.toNat < 9223372036854775808 ∧
      reference.offset.toNat + len.toNat ≤ sourceEntry.allocation.byteSize.bytes.toNat ∧
      sourceEntry.allocation.extra.locations.size = sourceEntry.allocation.byteSize ∧
      sourceEntry.allocation.extra.nodes.size + 2 < 65536 ∧
      sourceEntry.allocation.extra.nodes.size + 2 ≤ 4294967295 ∧
      tracker.global.nextPointerTag.value.toNat + 1 < 18446744073709551615)
    (geometry : let tick := RootZeroCompleteState.tick options remaining span machine
      tick.user.addresses = before.user.addresses ∧
      tick.user.payload.payload.user.types = before.user.payload.payload.user.types ∧
      tick.user.payload.payload.user.backend = .none ∧
      tick.user.payload.ghost = false ∧ tick.user.payload.validation = .Shallow ∧
      ((config options (remaining+1) span).terminators.getControl tick.user).checkedArithmetic = false ∧
      ((config options (remaining+1) span).terminators.getControl tick.user).gcInterval = 0 ∧
      tick.threads.fixedScheduling = true ∧ tick.dataRace = none ∧
      ∃ thread, tick.threads.activeThread? = some thread ∧ thread.topUserRelevantFrame = some 0)
    (mode : tracker.retagMode = .Default) :
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete reference.id tracker.global.nextPointerTag)
        (Size.ofBytes (reference.base+reference.offset))) len SharedReferenceMetadata.sharedLayout).imm
    let caller := GeneralBorrowForestSharedPreLenFrame.after frame (by rw [size]; decide) value
    ∃ (result : CompilerFrameContext.ActualFrame)
      (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (finalTree : BorrowTree) (held : MachineHooks.BorrowState) (child : UniIndex),
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] frame (RootZeroCompleteState.tick options remaining span machine))
        (Storage.withCurrent #[] result post) ∧
      result = LenCallResultFrame.resultFrame caller
        (by simpa [caller,GeneralBorrowForestSharedPreLenFrame.after,CopyHelperSteps.advance,
          ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using
          (show 11 < frame.locals.size by rw [size]; decide)) len ∧
      result.location = .mir ⟨3,0⟩ ∧
      post.memory = RetagEntry.updatedMemory (RootZeroCompleteState.tick options remaining span machine).memory
        reference.id sourceEntry finalTree ∧ post.borrowTracker = some held ∧ held.retagMode = tracker.retagMode ∧
      DuplicatePrefixBorrowContract.RuntimeFacts finalTree held.global ∧
      Nonempty (GeneralBorrowReadRowRange.Positive finalTree held.global.protectedTags child raw.selected
        raw.maximum reference.offset len) ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive finalTree held.global.protectedTags
        (some raw.parent) (some raw.selected) raw.maximum reference.offset len) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin finalTree raw.parent .Write
        reference.offset (reference.offset+len) ∧
      GeneralBorrowRawSharedToLenLedger.Graph sourceEntry.allocation.extra finalTree raw.selected tracker held ∧
      post.user.payload.ghost = false ∧ post.user.payload.validation = .Shallow ∧ post.dataRace = none ∧
      post.user.addresses = (RootZeroCompleteState.tick options remaining span machine).user.addresses ∧
      post.user.payload.payload.user.types = (RootZeroCompleteState.tick options remaining span machine).user.payload.payload.user.types ∧
      post.user.payload.payload.user.runtime.extras = (RootZeroCompleteState.tick options remaining span machine).user.payload.payload.user.runtime.extras ∧
      post.user.payload.payload.user.backend = .none ∧
      ((config options (remaining+1) span).terminators.getControl post.user).checkedArithmetic = false ∧
      ((config options (remaining+1) span).terminators.getControl post.user).gcInterval = 0 ∧
      post.threads.fixedScheduling = true ∧
      ∃ nextThread, post.threads.activeThread? = some nextThread ∧ nextThread.topUserRelevantFrame = some 0 := by
  obtain ⟨positive,nonzero,signedFits,_bounds,capacity,shortRoom,nodeRoom,tagRoom⟩ := bounds
  obtain ⟨addresses,types,backend,ghost,shallow,unchecked,noGc,fixed,race,
    thread,active,topZero⟩ := geometry
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
  obtain ⟨result,post,_tree,_held,_child,lenTrace,resultEq,_memory,_borrow,_modeAfter,_runtime,_range,
    _bothAfter,_activityAfter,_graphAfter,_ghost,_shallow,_race2,_address2,_types2,_extras2,_backend2,_unchecked2,_noGc2,_fixed2,_thread2⟩ :=
    GeneralBorrowRawSharedToLenLedger.complete options limits remaining span
      input.contract.model.preciseOff input.contract.model.implicitOff input.contract.model.debugOff
      input.contract.model.nullComparator (options.place.dynamicFuel-1) (options.limits.validation-1)
      (Nat.sub_add_cancel dynamicPositive).symm (Nat.sub_add_cancel validationPositive).symm
      reference.base reference.offset len reference.id sourceEntry positive nonzero signedFits #[] frame current
      body identity callee located tracker enabled mode fresh reference.tracker.global.nextPointerTag
      runtime raw rawTag rawOffset rawLen capacity validSource validDest sourceLive sourceCached
      destLive destUncached noClocks ghost shallow cached present race metadata notConstructed
      shortRoom nodeRoom tagRoom rfl (limits.callDispatch-1) (Nat.sub_add_cancel dispatchPositive).symm
      (DuplicatePrefixCallModel.sourceComparator options remaining span before input.contract.model)
      valid11 lenLive lenUncached backend unchecked noGc fixed thread active topZero both activity
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id tracker.global.nextPointerTag)
      (Size.ofBytes (reference.base+reference.offset))) len SharedReferenceMetadata.sharedLayout).imm
  let caller := GeneralBorrowForestSharedPreLenFrame.after frame validDest value
  refine ⟨result,post,_tree,_held,_child,lenTrace,?_,?_,_memory,_borrow,_modeAfter,_runtime,_range,
    _bothAfter,_activityAfter,_graphAfter,_ghost,_shallow,_race2,_address2,_types2,_extras2,_backend2,_unchecked2,_noGc2,_fixed2,_thread2⟩
  · simpa [caller,value] using resultEq
  · rw [resultEq]
    simp [LenCallResultFrame.resultFrame,GeneralBorrowForestSharedPreLenFrame.after]

end
end DuplicatePrefix.S02WildcardGenericSharedLenLedger

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardGenericSharedLenLedger.complete_at_site) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved generic shared length dependency {dependency}"
