import duplicate_prefix.GeneralBorrowRawSharedToLenMode
import duplicate_prefix.GeneralBorrowRawLenAcceptedFrame
import duplicate_prefix.GeneralBorrowRawSharedLenCompleteFrame
import duplicate_prefix.GeneralBorrowForestSharedPreLenFrame
import duplicate_prefix.LenCallResultFrame
namespace DuplicatePrefix.GeneralBorrowRawSharedToAcceptedFacts
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
    (count : UInt64) (countPositive : (0 : UInt64) < count) (within : count ≤ len/2) (size : frame.locals.size = 25)
    (live13 : (frame.locals[13]'(by omega)).value=.live (.immediate .uninit)) (cache13 : (frame.locals[13]'(by omega)).layout=none)
    (live0 : (frame.locals[0]'(by omega)).value=.live (.immediate .uninit)) (cache0 : (frame.locals[0]'(by omega)).layout=none)
    (live7 : (frame.locals[7]'(by omega)).value=.live (.immediate .uninit))
    (cache7 : (frame.locals[7]'(by omega)).layout=none)
    (dead15 : (frame.locals[15]'(by omega)).value=.dead) (cache15 : (frame.locals[15]'(by omega)).layout=none)
    (dead16 : (frame.locals[16]'(by omega)).value=.dead) (cache16 : (frame.locals[16]'(by omega)).layout=none)
    (live8 : (frame.locals[8]'(by omega)).value=.live (.immediate .uninit)) (cache8 : (frame.locals[8]'(by omega)).layout=none)
    (live9 : (frame.locals[9]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cache9 : (frame.locals[9]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (live10 : (frame.locals[10]'(by omega)).value=.live (.immediate .uninit)) (cache10 : (frame.locals[10]'(by omega)).layout=none)
    (allImmediate : CopyHelperCleanup.AllImmediate frame) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ (result : CompilerFrameContext.ActualFrame) (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (finalTree : BorrowTree) (held : MachineHooks.BorrowState) (child : UniIndex),
      SuccessfulTrace.Trace cfg limits (Storage.withCurrent frames frame machine) (Storage.withCurrent frames result post) ∧
      result.location = .mir ⟨6,7⟩ ∧ result.locals.size = 25 ∧
      result.body = frame.body ∧ result.bodyIdentity = frame.bodyIdentity ∧ result.functionInstance = frame.functionInstance ∧
      result.extra = frame.extra ∧ result.returnPlace = frame.returnPlace ∧ result.returnContinuation = frame.returnContinuation ∧
      result.vaList = frame.vaList ∧ result.localsIdentity = frame.localsIdentity ∧ result.trackCallerArg = frame.trackCallerArg ∧
      result.locals[1]? = frame.locals[1]? ∧ result.locals[2]? = frame.locals[2]? ∧
      result.locals[13]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ ∧
      result.locals[15]? = some ⟨.live (.immediate .uninit),none⟩ ∧ result.locals[16]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      (∀ index, 17 ≤ index → result.locals[index]? = frame.locals[index]?) ∧ CopyHelperCleanup.AllImmediate result ∧
      post.memory = RetagEntry.updatedMemory machine.memory id entry finalTree ∧ post.borrowTracker = some held ∧
      held.retagMode = tracker.retagMode ∧ DuplicatePrefixBorrowContract.RuntimeFacts finalTree held.global ∧
      Nonempty (GeneralBorrowReadRowRange.Positive finalTree held.global.protectedTags child raw.selected raw.maximum offset len) := by
  subst frames
  obtain ⟨returned,post,tree,held,child,lenTrace,returnedEq,memoryAfter,trackerAfter,modeAfter,runtimeAfter,positiveAfter,
    ghostAfter,shallowAfter,raceAfter,addresses,types,extras,backendAfter,uncheckedAfter,noGcAfter,fixedAfter,topAfter⟩ :=
    GeneralBorrowRawSharedToLenMode.complete options limits remaining span preciseOff implicitOff debugOff cmp
      dynamicFuel validityFuel fuelEq validationFuel base offset len id entry positive nonzero signedFits #[] frame machine
      sourceBody identity callee located tracker enabled defaultMode fresh parentTag runtime raw rawTag rawOffset rawLen capacity
      validSource validDest sourceLive sourceCached destLive destUncached noClocks ghost shallow cachedAddress present race metadata notConstructed
      shortRoom nodeRoom tagRoom rfl budget dispatch source valid11 lenLive lenUncached backend unchecked noGc fixed thread active topZero
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
  obtain ⟨result,data,frameFacts⟩ := GeneralBorrowRawLenAcceptedFrame.executes options limits remaining span source debugOff validityFuel validationFuel
    caller post len count countPositive within callerSize value callerLive
    ((congrArg LocalState.value (keep ⟨13,by decide⟩ (by decide))).trans live13)
    ((congrArg LocalState.layout (keep ⟨13,by decide⟩ (by decide))).trans cache13)
    ((congrArg LocalState.value (keep ⟨0,by decide⟩ (by decide))).trans live0)
    ((congrArg LocalState.layout (keep ⟨0,by decide⟩ (by decide))).trans cache0)
    ((congrArg LocalState.value (keep ⟨7,by decide⟩ (by decide))).trans live7)
    ((congrArg LocalState.layout (keep ⟨7,by decide⟩ (by decide))).trans cache7)
    ((congrArg LocalState.value (keep ⟨15,by decide⟩ (by decide))).trans dead15)
    ((congrArg LocalState.layout (keep ⟨15,by decide⟩ (by decide))).trans cache15)
    ((congrArg LocalState.value (keep ⟨16,by decide⟩ (by decide))).trans dead16)
    ((congrArg LocalState.layout (keep ⟨16,by decide⟩ (by decide))).trans cache16)
    ((congrArg LocalState.value (keep ⟨8,by decide⟩ (by decide))).trans live8)
    ((congrArg LocalState.layout (keep ⟨8,by decide⟩ (by decide))).trans cache8)
    ((congrArg LocalState.value (keep ⟨9,by decide⟩ (by decide))).trans live9)
    ((congrArg LocalState.layout (keep ⟨9,by decide⟩ (by decide))).trans cache9)
    ((congrArg LocalState.value (keep ⟨10,by decide⟩ (by decide))).trans live10)
    ((congrArg LocalState.layout (keep ⟨10,by decide⟩ (by decide))).trans cache10)
    sourceBody identity callee callerAll noClocks held trackerAfter (modeAfter.trans defaultMode) ghostAfter shallowAfter uncheckedAfter noGcAfter fixedAfter
  obtain ⟨guardTrace,bodyAfter,identityAfter,calleeAfter,extraAfter,placeAfter,continuationAfter,varargsAfter,localsIdentityAfter,
    trackAfter,sizeAfter,locationAfter,slot1,slot2,slot15,slot16,allAfter⟩ := data
  have ledger := GeneralBorrowRawLenAcceptedFrame.machine_ledger options remaining span post
  refine ⟨result,RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span post),tree,held,child,
    ?_,locationAfter,sizeAfter,bodyAfter,identityAfter,calleeAfter,extraAfter,placeAfter,continuationAfter,varargsAfter,localsIdentityAfter,trackAfter,?_,?_,frameFacts.slot13,slot15,slot16,?_,allAfter,ledger.1.trans memoryAfter,
    ledger.2.1.trans trackerAfter,modeAfter,runtimeAfter,positiveAfter⟩
  · apply SuccessfulTrace.append lenTrace
    simpa only [returnedEq] using guardTrace
  · exact slot1.trans ((LenCallResultFrame.other caller (by omega) len 1 (by decide)).trans (keepOpt 1 (by decide)))
  · exact slot2.trans ((LenCallResultFrame.other caller (by omega) len 2 (by decide)).trans (keepOpt 2 (by decide)))
  · intro index high
    exact (frameFacts.high index high).trans ((LenCallResultFrame.other caller (by omega) len index (by omega)).trans (keepOpt index (by omega)))
end
end DuplicatePrefix.GeneralBorrowRawSharedToAcceptedFacts
