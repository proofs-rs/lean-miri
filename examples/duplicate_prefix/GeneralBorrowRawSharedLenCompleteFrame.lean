import duplicate_prefix.GeneralBorrowRawSharedLenBodyResources
import duplicate_prefix.GeneralBorrowRawSharedLenReturnRuntime
import duplicate_prefix.GeneralBorrowRawSharedFnEntryOrder
import duplicate_prefix.GeneralBorrowRawSharedFnEntryResources
import duplicate_prefix.GeneralBorrowRawSharedFnEntryHidden
import duplicate_prefix.LenBodyFromEntry
namespace DuplicatePrefix.GeneralBorrowRawSharedLenCompleteFrame
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

    (stepRoom : entry.allocation.extra.nodes.size+1 < 65536) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let root := cachedCaller caller valid
    let borrowedTree := GeneralBorrowRawSharedFnEntryArgument.finalTree entry.allocation.extra tracker exprTag offset len
    let held := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag
    let borrowFrame := ({} : FrameState).addProtector id tracker.global.nextPointerTag
    let released := (borrowedTree.releaseProtector tracker.global.nextPointerTag held.global.protectedTags).tree
    ∃ result post child,
      SuccessfulTrace.Trace cfg limits (Storage.withCurrent frames caller beforeMachine)
        (Storage.withCurrent frames result post) ∧
      result = {PtrMetadataExecution.writeFrame root 11 (.scalar (.fromScalarInt (.ofUInt64 len)))
        (by simpa [root,cachedCaller,LocalPlaces.cachePlaceLayout] using valid) with location := .mir ⟨3,0⟩} ∧
      result.location = .mir ⟨3,0⟩ ∧
      post.memory = RetagEntry.updatedMemory beforeMachine.memory id entry released ∧
      post.borrowTracker = some {held with global := held.global.endCall borrowFrame} ∧
      DuplicatePrefixBorrowContract.RuntimeFacts released (held.global.endCall borrowFrame) ∧
      Nonempty (GeneralBorrowReadRowRange.Positive released (held.global.endCall borrowFrame).protectedTags
        child input.selected input.maximum offset len) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin released child .Write offset (offset+len) ∧
      post.user.payload.ghost = false ∧ post.user.payload.validation = .Shallow ∧ post.dataRace = none ∧
      post.user.addresses = beforeMachine.user.addresses ∧
      post.user.payload.payload.user.types = beforeMachine.user.payload.payload.user.types ∧
      post.user.payload.payload.user.runtime.extras = beforeMachine.user.payload.payload.user.runtime.extras ∧
      post.user.payload.payload.user.backend = .none ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl post.user).checkedArithmetic = false ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl post.user).gcInterval = 0 ∧
      post.threads.fixedScheduling = true ∧
      (frames=#[] → ∃ thread,post.threads.activeThread?=some thread ∧ thread.topUserRelevantFrame=some 0) := by
  let root := cachedCaller caller valid
  let borrowedTree := GeneralBorrowRawSharedFnEntryArgument.finalTree entry.allocation.extra tracker exprTag offset len
  let held := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag
  let borrowFrame := ({} : FrameState).addProtector id tracker.global.nextPointerTag
  obtain ⟨helper,bodyMachine,data,facts,cache,bodyRuntime,roots,growth,child,node,lookup,nodePresent,sameTag,hidden,⟨childPositive⟩,activity⟩ :=
    GeneralBorrowRawSharedLenBodyResources.before_return
      options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
      id entry base offset len exprTag positive nonzero signedFits frames caller machine tracker enabled defaultMode fresh runtime input
      parentTagEq offsetEq lenEq bounds allocationSize valid live uncached noClocks ghost shallow cachedAddress present race
      thread index current active top presentFrame metadata notConstructed sourceBody identity callee located source
      sourceValid sourceLive sourceCached backend beforeMachine machineEq unchecked noGc fixed
  obtain ⟨trace,helperLocation,retval,frameTracked,helperRace,destination,continuation,varargs,memoryEq,tracked,ghostAfter,shallowAfter,raceAfter,addresses,types,extras⟩ := data
  have rootValid : 11 < root.locals.size := by simpa [root,cachedCaller,LocalPlaces.cachePlaceLayout] using valid
  have rootLive : root.locals[11].value = .live (.immediate .uninit) := by simpa [root,cachedCaller,LocalPlaces.cachePlaceLayout] using live
  have rootCached : root.locals[11].layout = some RootCompilerFacts.usizeLayout := by simp [root,cachedCaller,LocalPlaces.cachePlaceLayout]
  have rootRace : root.extra.dataRace = none := noClocks
  have rootsExact : borrowedTree.roots = entry.allocation.extra.roots := roots
  have distinct : borrowedTree.roots.toList.Nodup := by rw [rootsExact];exact input.distinct
  have order : ∀ valid : 0 < borrowedTree.roots.size, input.selected ≠ borrowedTree.roots[0] →
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder borrowedTree := by
    simpa only [parentTagEq,offsetEq,lenEq] using
      GeneralBorrowRawSharedFnEntryOrder.order entry.allocation.extra tracker {} id runtime input
  have short : borrowedTree.nodes.size < 65536 := Nat.lt_of_le_of_lt growth stepRoom
  obtain ⟨result,post,step,resultEq,memoryAfter,trackerAfter,runtimeAfter,positiveAfter,activityAfter,postFacts,postTop⟩ :=
    GeneralBorrowRawSharedLenReturnRuntime.from_current options limits remaining span debugOff validityFuel validationEq
      frames root helper bodyMachine len _ facts helperLocation retval helperRace destination continuation varargs
      rootValid rootLive rootCached rootRace id tracker.global.nextPointerTag entry borrowedTree beforeMachine.memory
      memoryEq held borrowFrame tracked frameTracked rfl bodyRuntime child input.selected input.maximum offset childPositive
      node nodePresent sameTag hidden lookup distinct order short activity cache raceAfter ghostAfter shallowAfter
  refine ⟨result,post,child,SuccessfulTrace.append trace (.next step (.refl _)),resultEq,?_,memoryAfter,trackerAfter,runtimeAfter,positiveAfter,activityAfter,
    postFacts.ghost,postFacts.shallow,postFacts.race,postFacts.addresses.trans addresses,
    postFacts.types.trans types,postFacts.extras.trans extras,postFacts.backend,postFacts.unchecked,postFacts.noGc,
    postFacts.fixed,postTop⟩
  rw [resultEq]
end
end DuplicatePrefix.GeneralBorrowRawSharedLenCompleteFrame
