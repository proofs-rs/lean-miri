import duplicate_prefix.GeneralBorrowRawSharedLenCompleteFrame
import duplicate_prefix.GeneralBorrowRawLenRejectedFrame
import duplicate_prefix.GeneralBorrowRawSharedLenReturnRuntime
import duplicate_prefix.GeneralBorrowRawSharedFnEntryOrder
import duplicate_prefix.GeneralBorrowRawSharedFnEntryResources
import duplicate_prefix.GeneralBorrowRawSharedFnEntryHidden
import duplicate_prefix.LenBodyFromEntry
namespace DuplicatePrefix.GeneralBorrowRawSharedLenRejected
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess LenUncachedFrontend
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
open GeneralBorrowForestMixedLenBeforeReturn
theorem complete
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (exprTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (input : GeneralBorrowRawSharedFnEntry.Input entry.allocation.extra tracker.global)
    (parentTagEq : input.parentTag = exprTag) (offsetEq : input.offset = offset) (lenEq : input.len = len)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (allocationSize : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (valid : 11 < caller.locals.size)
    (live : caller.locals[11].value = .live (.immediate .uninit))
    (uncached : caller.locals[11].layout = none)
    (noClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (LenPush.pushed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller valid) machine)
      (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 11 RootCompilerFacts.usizeLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (presentFrame : (LenPush.pushed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller valid) machine)
      (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 11 RootCompilerFacts.usizeLayout).stackView).stack.frames[index]? = some current)
    (metadata : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller valid) machine)
      (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 11 RootCompilerFacts.usizeLayout).stackView current)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller valid) machine)
      (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 11 RootCompilerFacts.usizeLayout).stackView current)).entries.any (·.value.ty == 4) = false)
    (sourceBody : caller.body = RootBody.reflected.body.body)
    (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance)
    (located : caller.location = .mir ⟨2,12⟩)
    (source : PreparedContracts.SourceComparator)
    (sourceValid : 12 < caller.locals.size)
    (sourceLive : caller.locals[12].value = .live (.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id exprTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm))
    (sourceCached : caller.locals[12].layout = some SharedReferenceMetadata.sharedLayout)
    (backend : machine.user.payload.payload.user.backend = .none)
    (beforeMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (machineEq : machine = PtrMetadataReturn.accountedMachine options remaining span beforeMachine)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).gcInterval = 0)
    (fixed : beforeMachine.threads.fixedScheduling = true)

    (stepRoom : entry.allocation.extra.nodes.size+1 < 65536)
    (rootCall : frames = #[]) (count : UInt64) (rejected : count > len/2)
    (callerSize : caller.locals.size = 25)
    (live13 : (caller.locals[13]'(by omega)).value=.live (.immediate .uninit)) (cache13 : (caller.locals[13]'(by omega)).layout=none)
    (live0 : (caller.locals[0]'(by omega)).value=.live (.immediate .uninit)) (cache0 : (caller.locals[0]'(by omega)).layout=none)
    (live7 : (caller.locals[7]'(by omega)).value=.live (.immediate .uninit))
    (live8 : (caller.locals[8]'(by omega)).value=.live (.immediate .uninit)) (cache8 : (caller.locals[8]'(by omega)).layout=none)
    (live9 : (caller.locals[9]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cache9 : (caller.locals[9]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (live10 : (caller.locals[10]'(by omega)).value=.live (.immediate .uninit)) (cache10 : (caller.locals[10]'(by omega)).layout=none)
    (allImmediate : CopyHelperCleanup.AllImmediate caller) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let borrowedTree := GeneralBorrowRawSharedFnEntryArgument.finalTree entry.allocation.extra tracker exprTag offset len
    let held := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag
    let borrowFrame := ({} : FrameState).addProtector id tracker.global.nextPointerTag
    let released := (borrowedTree.releaseProtector tracker.global.nextPointerTag held.global.protectedTags).tree
    ∃ result post child,
      SuccessfulTrace.Trace cfg limits (Storage.withCurrent frames caller beforeMachine)
        (Storage.withCurrent frames result post) ∧
      result.location = .mir ⟨10,0⟩ ∧ result.locals.size = 25 ∧
      result.locals[0]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ ∧
      post.memory = RetagEntry.updatedMemory beforeMachine.memory id entry released ∧
      post.borrowTracker = some {held with global := held.global.endCall borrowFrame} ∧
      DuplicatePrefixBorrowContract.RuntimeFacts released (held.global.endCall borrowFrame) ∧
      Nonempty (GeneralBorrowReadRowRange.Positive released (held.global.endCall borrowFrame).protectedTags
        child input.selected input.maximum offset len) ∧
      CopyHelperCleanup.AllImmediate result := by
  subst frames
  obtain ⟨returned,post,child,trace,returnedEq,location,memoryAfter,trackerAfter,runtimeAfter,positiveAfter,activityAfter,
    ghostAfter,shallowAfter,raceAfter,addresses,types,extras,backendAfter,uncheckedAfter,noGcAfter,fixedAfter,topAfter⟩ :=
    GeneralBorrowRawSharedLenCompleteFrame.complete options limits remaining budget dispatchFuel span ctx debugOff cmp
      dynamicFuel validityFuel fuelEq validationEq id entry base offset len exprTag positive nonzero signedFits
      #[] caller machine tracker enabled defaultMode fresh runtime input parentTagEq offsetEq lenEq bounds allocationSize
      valid live uncached noClocks ghost shallow cachedAddress present race thread index current active top presentFrame metadata notConstructed
      sourceBody identity callee located source sourceValid sourceLive sourceCached backend beforeMachine machineEq unchecked noGc fixed stepRoom
  let held := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag
  let borrowFrame := ({} : FrameState).addProtector id tracker.global.nextPointerTag
  have returnedFrame : returned = LenCallResultFrame.resultFrame caller valid len := by
    simpa only [LenCallResultFrame.resultFrame,ActualLocalCopy.written,LenUncachedFrontend.cachedCaller,
      PtrMetadataExecution.writeFrame] using returnedEq
  obtain ⟨result,guardTrace,body,identityAfter,calleeAfter,extraAfter,returnPlaceAfter,continuationAfter,varargsAfter,
    localsIdentityAfter,sizeAfter,locationAfter,valueAfter,allAfter⟩ :=
    GeneralBorrowRawLenRejectedFrame.executes options limits remaining span source debugOff validityFuel validationEq
      caller post len count rejected callerSize _ sourceLive live13 cache13 live0 cache0 live7
      live8 cache8 live9 cache9 live10 cache10 sourceBody identity callee allImmediate noClocks
      {held with global := held.global.endCall borrowFrame} trackerAfter defaultMode ghostAfter shallowAfter uncheckedAfter noGcAfter fixedAfter
  have ledger := GeneralBorrowRawLenRejectedFrame.machine_ledger options remaining span post
  refine ⟨result,RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span
    (RootZeroCompleteState.tick options remaining span post)),child,?_,locationAfter,sizeAfter,valueAfter,
    ledger.1.trans memoryAfter,ledger.2.1.trans trackerAfter,runtimeAfter,positiveAfter,allAfter⟩
  apply SuccessfulTrace.append trace
  simpa only [returnedFrame] using guardTrace
end
end DuplicatePrefix.GeneralBorrowRawSharedLenRejected
