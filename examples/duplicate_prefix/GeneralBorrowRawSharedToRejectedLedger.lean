import duplicate_prefix.GeneralBorrowRawSharedToLenLedger
import duplicate_prefix.GeneralBorrowRawSharedToLenMode
import duplicate_prefix.GeneralBorrowRawLenRejectedFrame
import duplicate_prefix.GeneralBorrowRawSharedLenCompleteFrame
import duplicate_prefix.GeneralBorrowForestSharedPreLenFrame
import duplicate_prefix.LenCallResultFrame
namespace DuplicatePrefix.GeneralBorrowRawSharedToRejectedLedger
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext RootReferenceInfo RootReferenceTrees GeneralBorrowRawSharedExpression
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
theorem complete
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (preciseOff : options.retag.preciseInteriorMut = false)
    (implicitOff : options.retag.implicitWrites = false)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationFuel : options.limits.validation = validityFuel+1)
    (base offset len : UInt64)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (located : frame.location = .mir (RootReferenceFacts.location true))
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (parentTag : BorTag)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (raw : GeneralBorrowRawShared.Input entry.allocation.extra tracker.global)
    (rawTag : raw.parentTag = parentTag) (rawOffset : raw.offset = offset) (rawLen : raw.len = len)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (validSource : (1 : MIR.LocalId) < frame.locals.size) (validDest : (RootReferenceFacts.destination true) < frame.locals.size)
    (sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference)
    (destLive : frame.locals[RootReferenceFacts.destination true].value = .live (.immediate .uninit))
    (destUncached : frame.locals[RootReferenceFacts.destination true].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false)
    (shortRoom : entry.allocation.extra.nodes.size+2 < 65536)
    (nodeRoom : entry.allocation.extra.nodes.size+2 ≤ 4294967295)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615)
    (rootCall : frames = #[]) (budget : Nat) (dispatch : limits.callDispatch = budget+1)
    (source : PreparedContracts.SourceComparator)
    (valid11 : 11 < frame.locals.size) (lenLive : frame.locals[11].value = .live (.immediate .uninit))
    (lenUncached : frame.locals[11].layout = none)
    (backend : machine.user.payload.payload.user.backend = .none)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (thread : Miri.Concurrency.ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (topZero : thread.topUserRelevantFrame = some 0)
    (count : UInt64) (rejected : count > len/2) (size : frame.locals.size = 25)
    (live13 : (frame.locals[13]'(by omega)).value=.live (.immediate .uninit)) (cache13 : (frame.locals[13]'(by omega)).layout=none)
    (live0 : (frame.locals[0]'(by omega)).value=.live (.immediate .uninit)) (cache0 : (frame.locals[0]'(by omega)).layout=none)
    (live7 : (frame.locals[7]'(by omega)).value=.live (.immediate .uninit))
    (live8 : (frame.locals[8]'(by omega)).value=.live (.immediate .uninit)) (cache8 : (frame.locals[8]'(by omega)).layout=none)
    (live9 : (frame.locals[9]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cache9 : (frame.locals[9]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (live10 : (frame.locals[10]'(by omega)).value=.live (.immediate .uninit)) (cache10 : (frame.locals[10]'(by omega)).layout=none)
    (allImmediate : CopyHelperCleanup.AllImmediate frame)
    (both : DuplicatePrefixBorrowAuthorization.Positive entry.allocation.extra tracker.global.protectedTags
      (some raw.parent) (some raw.selected) raw.maximum offset len)
    (activity : GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra raw.parent .Write
      offset (offset+len)) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ (result : CompilerFrameContext.ActualFrame) (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (finalTree : BorrowTree) (held : MachineHooks.BorrowState) (child : UniIndex),
      SuccessfulTrace.Trace cfg limits (Storage.withCurrent frames frame machine) (Storage.withCurrent frames result post) ∧
      result.location = .mir ⟨10,0⟩ ∧ result.locals.size = 25 ∧
      result.body = frame.body ∧ result.bodyIdentity = frame.bodyIdentity ∧ result.functionInstance = frame.functionInstance ∧
      result.extra = frame.extra ∧ result.returnPlace = frame.returnPlace ∧ result.returnContinuation = frame.returnContinuation ∧
      result.vaList = frame.vaList ∧ result.localsIdentity = frame.localsIdentity ∧
      result.locals[0]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ ∧
      CopyHelperCleanup.AllImmediate result ∧
      post.memory = RetagEntry.updatedMemory machine.memory id entry finalTree ∧ post.borrowTracker = some held ∧
      held.retagMode = tracker.retagMode ∧ DuplicatePrefixBorrowContract.RuntimeFacts finalTree held.global ∧
      Nonempty (GeneralBorrowReadRowRange.Positive finalTree held.global.protectedTags child raw.selected raw.maximum offset len) ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive finalTree held.global.protectedTags
        (some raw.parent) (some raw.selected) raw.maximum offset len) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin finalTree raw.parent .Write offset (offset+len) ∧
      GeneralBorrowRawSharedToLenLedger.Graph entry.allocation.extra finalTree raw.selected tracker held := by
  subst frames
  obtain ⟨returned,post,tree,held,child,lenTrace,returnedEq,memoryAfter,trackerAfter,modeAfter,runtimeAfter,positiveAfter,bothAfter,activityAfter,graphAfter,
    ghostAfter,shallowAfter,raceAfter,addresses,types,extras,backendAfter,uncheckedAfter,noGcAfter,fixedAfter,topAfter⟩ :=
    GeneralBorrowRawSharedToLenLedger.complete options limits remaining span preciseOff implicitOff debugOff cmp
      dynamicFuel validityFuel fuelEq validationFuel base offset len id entry positive nonzero signedFits #[] frame machine
      sourceBody identity callee located tracker enabled defaultMode fresh parentTag runtime raw rawTag rawOffset rawLen capacity
      validSource validDest sourceLive sourceCached destLive destUncached noClocks ghost shallow cachedAddress present race metadata notConstructed
      shortRoom nodeRoom tagRoom rfl budget dispatch source valid11 lenLive lenUncached backend unchecked noGc fixed thread active topZero both activity
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
  let caller := GeneralBorrowForestSharedPreLenFrame.after frame validDest value
  have callerSize : caller.locals.size = 25 := by simpa [caller,GeneralBorrowForestSharedPreLenFrame.after,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using size
  have original (i : Fin 25) : i.val < frame.locals.size := by rw [size];exact i.isLt
  have bounded (i : Fin 25) : i.val < caller.locals.size := by rw [callerSize];exact i.isLt
  have keepOpt (i : Nat) (different : i ≠ 12) : caller.locals[i]? = frame.locals[i]? := by
    simp [caller,GeneralBorrowForestSharedPreLenFrame.after,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem?_set,different,Ne.symm different]
  have keep (i : Fin 25) (different : i.val ≠ 12) : caller.locals[i.val]'(bounded i) = frame.locals[i.val]'(original i) := by
    exact Option.some.inj ((Array.getElem?_eq_getElem (bounded i)).symm.trans ((keepOpt i.val different).trans (Array.getElem?_eq_getElem (original i))))
  have callerLive : caller.locals[12].value = .live (.immediate value) := by
    simp [caller,GeneralBorrowForestSharedPreLenFrame.after,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout]
  have callerAll : CopyHelperCleanup.AllImmediate caller := CopyHelperCleanup.all_immediate_written frame 12 SharedReferenceMetadata.sharedLayout value validDest allImmediate
  obtain ⟨result,guardTrace,bodyAfter,identityAfter,calleeAfter,extraAfter,placeAfter,continuationAfter,varargsAfter,
    localsIdentityAfter,sizeAfter,locationAfter,valueAfter,allAfter⟩ :=
    GeneralBorrowRawLenRejectedFrame.executes options limits remaining span source debugOff validityFuel validationFuel
      caller post len count rejected callerSize value callerLive
      ((congrArg LocalState.value (keep ⟨13,by decide⟩ (by decide))).trans live13)
      ((congrArg LocalState.layout (keep ⟨13,by decide⟩ (by decide))).trans cache13)
      ((congrArg LocalState.value (keep ⟨0,by decide⟩ (by decide))).trans live0)
      ((congrArg LocalState.layout (keep ⟨0,by decide⟩ (by decide))).trans cache0)
      ((congrArg LocalState.value (keep ⟨7,by decide⟩ (by decide))).trans live7)
      ((congrArg LocalState.value (keep ⟨8,by decide⟩ (by decide))).trans live8)
      ((congrArg LocalState.layout (keep ⟨8,by decide⟩ (by decide))).trans cache8)
      ((congrArg LocalState.value (keep ⟨9,by decide⟩ (by decide))).trans live9)
      ((congrArg LocalState.layout (keep ⟨9,by decide⟩ (by decide))).trans cache9)
      ((congrArg LocalState.value (keep ⟨10,by decide⟩ (by decide))).trans live10)
      ((congrArg LocalState.layout (keep ⟨10,by decide⟩ (by decide))).trans cache10)
      sourceBody identity callee callerAll noClocks held trackerAfter (modeAfter.trans defaultMode) ghostAfter shallowAfter uncheckedAfter noGcAfter fixedAfter
  have ledger := GeneralBorrowRawLenRejectedFrame.machine_ledger options remaining span post
  refine ⟨result,RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span post)),tree,held,child,
    ?_,locationAfter,sizeAfter,bodyAfter,identityAfter,calleeAfter,extraAfter,placeAfter,continuationAfter,varargsAfter,localsIdentityAfter,
    valueAfter,allAfter,ledger.1.trans memoryAfter,ledger.2.1.trans trackerAfter,modeAfter,runtimeAfter,positiveAfter,bothAfter,activityAfter,graphAfter⟩
  apply SuccessfulTrace.append lenTrace
  simpa only [returnedEq] using guardTrace
end
end DuplicatePrefix.GeneralBorrowRawSharedToRejectedLedger
