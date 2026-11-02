import duplicate_prefix.PositiveLenPost
import duplicate_prefix.EmptyForestPoolRootLenCall
import duplicate_prefix.EmptyForestSharedPoolReleaseFrame
import duplicate_prefix.GenericRootRejectedExitCore
import duplicate_prefix.RootZeroInvocationState
namespace DuplicatePrefix.EmptyForestPoolRejectedAfterLen
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess LenUncachedFrontend
open PhysicalMachineWrite
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem complete
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (rootTag parentTag newTag : BorTag)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset : UInt64)
    (input : EmptyForestSharedPool.Input entry.allocation.extra parentTag newTag)
    (rootIndex : UniIndex) (rootNode : TreeNode)
    (rootTagged : entry.allocation.extra.indexOfTag rootTag = some rootIndex)
    (rootPresent : entry.allocation.extra.nodeAt rootIndex = some rootNode)
    (rootUnexposed : rootNode.isExposed = false)
    (rootAbsent : ∀ position (valid : position < entry.allocation.extra.locations.entries.size),
      entry.allocation.extra.locations.entries[position].data.perms.get rootIndex = none)
    (nonzero : base+offset ≠ 0)
    (caller : CompilerFrameContext.ActualFrame)
    (beforeMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : beforeMachine.borrowTracker = some tracker)
    (nextTag : tracker.global.nextPointerTag = newTag)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (valid : 11 < caller.locals.size)
    (live : caller.locals[11].value = .live (.immediate .uninit))
    (uncached : caller.locals[11].layout = none)
    (noClocks : caller.extra.dataRace = none)
    (ghost : beforeMachine.user.payload.ghost = false) (shallow : beforeMachine.user.payload.validation = .Shallow)
    (cachedAddress : beforeMachine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : beforeMachine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : beforeMachine.dataRace = none)
    (thread : Miri.Concurrency.ThreadRecord)
    (active : beforeMachine.threads.activeThread? = some thread)
    (cachedThread : thread.topUserRelevantFrame = some 0)
    (metadata : beforeMachine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : beforeMachine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (sourceBody : caller.body = RootBody.reflected.body.body)
    (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance)
    (located : caller.location = .mir ⟨2,12⟩)
    (source : PreparedContracts.SourceComparator)
    (sourceValid : 12 < caller.locals.size)
    (sourceLive : caller.locals[12].value = .live (.immediate (RetagReferencePlace.sliceValue (ActualReferenceContext.config options remaining span).access.runtime.base
      (Pointer.new (.concrete id (parentTag)) (Size.ofBytes (base+offset))) 0 SharedReferenceMetadata.sharedLayout).imm))
    (sourceCached : caller.locals[12].layout = some SharedReferenceMetadata.sharedLayout)
    (backend : beforeMachine.user.payload.payload.user.backend = .none)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).gcInterval = 0)
    (fixed : beforeMachine.threads.fixedScheduling = true)
    (inputCount : UInt64) (rejected : inputCount > 0/2)
    (frameSize : caller.locals.size = 25) (allImmediate : CopyHelperCleanup.AllImmediate caller)
    (live0 : (caller.locals[0]'(by omega)).value = .live (.immediate .uninit))
    (cache0 : (caller.locals[0]'(by omega)).layout = none)
    (live7 : (caller.locals[7]'(by omega)).value = .live (.immediate .uninit))
    (live8 : (caller.locals[8]'(by omega)).value = .live (.immediate .uninit)) (cache8 : (caller.locals[8]'(by omega)).layout = none)
    (live9 : (caller.locals[9]'(by omega)).value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 inputCount)))))
    (cache9 : (caller.locals[9]'(by omega)).layout = some RootCompilerFacts.usizeLayout)
    (live10 : (caller.locals[10]'(by omega)).value = .live (.immediate .uninit)) (cache10 : (caller.locals[10]'(by omega)).layout = none)
    (live13 : (caller.locals[13]'(by omega)).value = .live (.immediate .uninit)) (cache13 : (caller.locals[13]'(by omega)).layout = none)
    (borrowFrame : FrameState) (frameBorrow : caller.extra.borrowTracker = some borrowFrame)
    (slotId : AllocId) (slotEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (slotRoot slotChild : BorTag) (slotBase : UInt64)
    (owned : borrowFrame.protectedTags = #[(id,rootTag),(slotId,slotChild)])
    (place : MPlaceTy Provenance) (slotLayout : place.layout = RootCompilerFacts.boolLayout)
    (slotPointer : place.mplace.ptr = Pointer.new (some (.concrete slotId slotRoot)) (Size.ofBytes slotBase))
    (slotAligned : place.mplace.misaligned = none)
    (slotCached : beforeMachine.user.addresses.baseAddr.find? (fun row => row.allocId == slotId) = some ⟨slotId,slotBase⟩)
    (slotPresent : beforeMachine.memory.live.find? (fun row => row.1 == slotId) = some (slotId,slotEntry))
    (separate : slotId ≠ id)
    (slotTree : slotEntry.allocation.extra = PhysicalMachineWrite.slotTree slotRoot slotChild 1 true)
    (slotSize : slotEntry.allocation.byteSize = Size.ofBytes 1)
    (slotMutable : slotEntry.allocation.mutability = .Mut)
    (slotStorage : slotEntry.allocation.len = slotEntry.allocation.byteSize.bytes.toNat)
    (slotMask : slotEntry.allocation.initializationMask.len = slotEntry.allocation.byteSize)
    (slotWellFormed : InitMaskCopy.WellFormed slotEntry.allocation.initializationMask)
    (slotProvenance : slotEntry.allocation.provenanceMap = ProvenanceMap.new)
    (slotExtras : beforeMachine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == slotId) = some (slotId,⟨none,#[]⟩))
    (slotFree : tracker.global.protectedTags.contains slotRoot = false)
    (slotHeld : tracker.global.protectedTags.contains slotChild = true)
    (slotDistinct : slotRoot ≠ slotChild)
    (slotRootNot3 : slotRoot ≠ newTag) (slotChildNot3 : slotChild ≠ newTag)
    (continuation : caller.returnContinuation = .stop true)
    (destination : caller.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩)
    (varargs : caller.vaList = #[])
    (fits : slotBase.toNat+1 < 2^64) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let initial := Storage.withCurrent #[] caller beforeMachine
    let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit := ⟨config,limits,fun _ _ => True⟩
    ∃ done, SuccessfulTrace.Trace config limits initial done ∧
      ExecutionMachine.step config limits () done = (done,.ok false) ∧
      done.stack.frames = #[] ∧
      CallSafety.NoUBBeforeReturn safety 1 initial := by
  dsimp only
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  obtain ⟨finalMachine,lenTrace,memoryEq,trackerEq,ghostEq,shallowEq,raceEq,fixedEq,uncheckedEq,noGcEq,addrEq,typesEq,backendEq,extrasEq,finalThread,finalActive⟩ :=
    EmptyForestPoolRootLenCall.returns_zero options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq parentTag newTag
      id entry base offset input nonzero caller beforeMachine tracker enabled nextTag defaultMode fresh
      valid live uncached noClocks ghost shallow cachedAddress present race thread active cachedThread metadata notConstructed
      sourceBody identity callee located source sourceValid sourceLive sourceCached backend unchecked noGc fixed
  let afterFrame := EmptyForestPoolLenCallReturn.resultFrame caller valid 0
  let afterTracker := PositiveLenPost.trackerAfter tracker fresh id
  let bM := RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span
    (RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span finalMachine)))
  let bufferTree := input.after
  let bufferEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind := {entry with allocation := entry.allocation.setExtra bufferTree}
  let releasedBuffer := StackPopRelease.commitTree bM.memory id bufferEntry bufferEntry.allocation.extra
  let releasedMemory := StackPopRelease.commitTree releasedBuffer slotId slotEntry slotEntry.allocation.extra
  let postTracker := {afterTracker with global := afterTracker.global.endCall borrowFrame}
  let popped := GenericPopFrame.afterRelevanceAt #[] afterFrame (ActualPopPlan.released bM releasedMemory afterTracker borrowFrame)
    (finalThread.topUserRelevantFrame.getD 0)
  let state : MachineHooks.State MiriMemoryKind Machine.RootUser := ⟨⟨#[]⟩,popped⟩
  have bufferPresent : finalMachine.memory.live.find? (fun row => row.1 == id) = some (id,bufferEntry) := by
    rw [memoryEq]
    exact PositiveLenPost.buffer_lookup _ id entry _ bufferTree
  have slotPresentAfter : finalMachine.memory.live.find? (fun row => row.1 == slotId) = some (slotId,slotEntry) := by
    rw [memoryEq]
    exact PositiveLenPost.other_lookup _ id slotId entry slotEntry _ bufferTree separate slotPresent
  have releasedPresent : releasedMemory.live.find? (fun row => row.1 == slotId) = some (slotId,slotEntry) := by
    have self : slotEntry.allocation.setExtra slotEntry.allocation.extra = slotEntry.allocation := by cases slotEntry.allocation;rfl
    simpa only [self] using StackPopRelease.lookup_commit_same releasedBuffer slotId slotEntry slotEntry.allocation.extra
  have heldFree : afterTracker.global.protectedTags.contains slotRoot = false := by
    unfold afterTracker PositiveLenPost.trackerAfter
    rw [StackPopRelease.end_call_contains]
    have notOwned : slotRoot ∉ (({} : FrameState).addProtector id tracker.global.nextPointerTag).protectedTags.toList.map Prod.snd := by simp [FrameState.addProtector,nextTag,slotRootNot3]
    rw [ite_eq_right notOwned]
    change (tracker.global.protectedTags.insert tracker.global.nextPointerTag .StrongProtector).contains slotRoot = false
    have different : slotRoot ≠ tracker.global.nextPointerTag := by rw [nextTag];exact slotRootNot3
    rw [ProtectorInsertion.contains_other tracker.global.protectedTags tracker.global.nextPointerTag
      slotRoot .StrongProtector different]
    exact slotFree
  have heldChild : afterTracker.global.protectedTags.contains slotChild = true := by
    unfold afterTracker PositiveLenPost.trackerAfter
    rw [StackPopRelease.end_call_contains]
    have notOwned : slotChild ∉ (({} : FrameState).addProtector id tracker.global.nextPointerTag).protectedTags.toList.map Prod.snd := by simp [FrameState.addProtector,nextTag,slotChildNot3]
    rw [ite_eq_right notOwned]
    change (tracker.global.protectedTags.insert tracker.global.nextPointerTag .StrongProtector).contains slotChild = true
    have different : slotChild ≠ tracker.global.nextPointerTag := by rw [nextTag];exact slotChildNot3
    rw [ProtectorInsertion.contains_other tracker.global.protectedTags tracker.global.nextPointerTag
      slotChild .StrongProtector different]
    exact slotHeld
  have profile : StackPopRelease.Plan afterTracker.global.protectedTags borrowFrame.protectedTags.toList bM.memory releasedMemory := by
    rw [owned]
    apply StackPopRelease.Plan.live id rootTag bufferEntry bufferEntry.allocation.extra [(slotId,slotChild)] bM.memory releasedMemory bufferPresent
    · exact EmptyForestSharedPoolReleaseFrame.release input rootTag rootIndex rootNode rootTagged rootPresent rootUnexposed rootAbsent afterTracker.global.protectedTags
    · apply StackPopRelease.Plan.live slotId slotChild slotEntry slotEntry.allocation.extra [] releasedBuffer releasedMemory
        (StackPopRelease.lookup_commit_other bM.memory id slotId bufferEntry slotEntry bufferEntry.allocation.extra separate slotPresentAfter)
      · rw [slotTree]
        exact ReturnTreeAccess.slot_release slotRoot slotChild 1 true afterTracker.global.protectedTags heldFree heldChild slotDistinct (by decide)
      · exact .nil _
  have sizeAfter : afterFrame.locals.size = 25 := (LenCallResultFrame.size caller valid 0).trans frameSize
  have va (i : Fin 25) : i.val < afterFrame.locals.size := by rw [sizeAfter];exact i.isLt
  have vc (i : Fin 25) : i.val < caller.locals.size := by rw [frameSize];exact i.isLt
  have kept (i : Fin 25) (other : i.val ≠ 11) : (afterFrame.locals[i.val]'(va i)) = caller.locals[i.val]'(vc i) := by
    exact Option.some.inj ((Array.getElem?_eq_getElem (va i)).symm.trans ((LenCallResultFrame.other caller valid 0 i.val other).trans (Array.getElem?_eq_getElem (vc i))))
  have lenSlot : afterFrame.locals[11]'(va ⟨11,by decide⟩) = ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 0)))),some RootCompilerFacts.usizeLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (va ⟨11,by decide⟩)).symm.trans (LenCallResultFrame.value caller valid 0))
  have sourceSlot : afterFrame.locals[12]'(va ⟨12,by decide⟩) = caller.locals[12]'(vc ⟨12,by decide⟩) := kept ⟨12,by decide⟩ (by decide)
  have stateUser : state.machine.user = bM.user := by
    dsimp only [state,popped,GenericPopFrame.afterRelevanceAt]
    split <;> rfl
  have stateRace : state.machine.dataRace = none := by
    dsimp only [state,popped,GenericPopFrame.afterRelevanceAt]
    split <;> exact raceEq
  have stateBorrow : state.machine.borrowTracker = some postTracker := by
    dsimp only [state,popped,GenericPopFrame.afterRelevanceAt]
    split <;> rfl
  have addrState : state.machine.user.addresses = beforeMachine.user.addresses := by
    rw [stateUser]
    change bM.user.addresses = _
    dsimp only [bM]
    rw [(RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.1,
      (RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.1,
      (RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.1,
      (RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.1]
    exact addrEq
  have backendState : state.machine.user.payload.payload.user.backend = .none := by
    rw [stateUser]
    change bM.user.payload.payload.user.backend = _
    dsimp only [bM]
    rw [(RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.2.1,
      (RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.2.1,
      (RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.2.1,
      (RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.2.1]
    rw [backendEq]
    exact backend
  have extrasState : state.machine.user.payload.payload.user.runtime.extras = beforeMachine.user.payload.payload.user.runtime.extras := by
    rw [stateUser]
    change bM.user.payload.payload.user.runtime.extras = _
    dsimp only [bM]
    rw [(RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.2.2,
      (RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.2.2,
      (RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.2.2,
      (RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.2.2]
    exact extrasEq
  have ghostState : state.machine.user.payload.ghost = false := by
    rw [stateUser]
    change bM.user.payload.ghost = false
    dsimp only [bM]
    rw [RootZeroCompleteState.tick_ghost,RootZeroCompleteState.tick_ghost,RootZeroCompleteState.tick_ghost,RootZeroCompleteState.tick_ghost]
    exact ghostEq
  have shallowState : state.machine.user.payload.validation = .Shallow := by
    rw [stateUser]
    change bM.user.payload.validation = .Shallow
    dsimp only [bM]
    rw [RootZeroCompleteState.tick_shallow,RootZeroCompleteState.tick_shallow,RootZeroCompleteState.tick_shallow,RootZeroCompleteState.tick_shallow]
    exact shallowEq
  have rootFree : postTracker.global.protectedTags.contains slotRoot = false := by
    rw [StackPopRelease.end_call_contains]
    split
    · rfl
    · exact heldFree
  have childFree : postTracker.global.protectedTags.contains slotChild = false := by
    rw [StackPopRelease.end_call_contains]
    simp [owned]
  have fields := CanonicalConfigFacts.actual_fields options () (remaining+1) span
  have innerFields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨outer,outerAccess,outerArithmetic,_⟩ := fields.canonicalCopy
  obtain ⟨inner,innerAccess,innerArithmetic,_⟩ := innerFields.canonicalCopy
  have outerWidth : outer.pointers.arithmetic=⟨Size.ofBytes 8⟩ := outerArithmetic.symm.trans (CanonicalConfigFacts.actual_arithmetic options () (remaining+1) span)
  have innerWidth : inner.pointers.arithmetic=⟨Size.ofBytes 8⟩ := innerArithmetic.symm.trans (CanonicalConfigFacts.actual_arithmetic options () remaining span)
  have outerRuntime : outer.access.runtime=PreparedReflection.actual.runtime.target :=
    (congrArg (fun access => access.runtime) outerAccess).symm.trans (CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span)
  have innerRuntime : inner.access.runtime=PreparedReflection.actual.runtime.target :=
    (congrArg (fun access => access.runtime) innerAccess).symm.trans (CanonicalConfigFacts.actual_access_runtime options () remaining span)
  have endpoint : (allocRange place.mplace.ptr.offset (Size.ofBytes 1)).endExclusive=.ok (Size.ofBytes (slotBase+1)) := by
    rw [slotPointer]
    have added := size_add_ok (Size.ofBytes slotBase) (Size.ofBytes 1) (by simpa only [Size.ofBytes,UInt64.toNat_one] using fits)
    simp only [Pointer.new,allocRange,AllocRange.endExclusive,AllocRange.end,added,Except.mapError]
    rfl
  obtain ⟨updated,exitTrace,terminal,safe,props⟩ := GenericRootRejectedExitCore.complete outer inner options remaining span innerAccess innerWidth
    (by rw [innerRuntime];rfl) (by rw [innerRuntime,outerRuntime]) limits validityFuel debugOff validationEq
    afterFrame finalMachine bM rfl uncheckedEq noGcEq fixedEq afterTracker borrowFrame trackerEq frameBorrow releasedMemory profile finalThread finalActive state rfl
    sourceBody identity callee rfl sizeAfter source 0 inputCount rejected
    (RetagReferencePlace.sliceValue (ActualReferenceContext.config options remaining span).access.runtime.base (Pointer.new (.concrete id (parentTag)) (Size.ofBytes (base+offset))) 0 SharedReferenceMetadata.sharedLayout).imm
    ((congrArg (fun row => row.value) sourceSlot).trans sourceLive)
    ((congrArg (fun row => row.value) (kept ⟨13,by decide⟩ (by decide))).trans live13) ((congrArg (fun row => row.layout) (kept ⟨13,by decide⟩ (by decide))).trans cache13)
    ((congrArg (fun row => row.value) (kept ⟨7,by decide⟩ (by decide))).trans live7)
    ((congrArg (fun row => row.value) (kept ⟨8,by decide⟩ (by decide))).trans live8) ((congrArg (fun row => row.layout) (kept ⟨8,by decide⟩ (by decide))).trans cache8)
    ((congrArg (fun row => row.value) (kept ⟨9,by decide⟩ (by decide))).trans live9) ((congrArg (fun row => row.layout) (kept ⟨9,by decide⟩ (by decide))).trans cache9)
    ((congrArg (fun row => row.value) (kept ⟨10,by decide⟩ (by decide))).trans live10) ((congrArg (fun row => row.layout) (kept ⟨10,by decide⟩ (by decide))).trans cache10)
    (congrArg (fun row => row.value) lenSlot) (congrArg (fun row => row.layout) lenSlot)
    ghostEq shallowEq defaultMode (va ⟨0,by decide⟩) noClocks continuation (LenCallResultFrame.all_immediate caller valid 0 allImmediate) varargs
    place slotId slotRoot slotChild true slotBase 1 slotEntry postTracker
    ((congrArg (fun row => row.value) (kept ⟨0,by decide⟩ (by decide))).trans live0) ((congrArg (fun row => row.layout) (kept ⟨0,by decide⟩ (by decide))).trans cache0)
    rfl slotLayout outerWidth (by decide) (by decide) (by rw [addrState];exact slotCached) slotPresentAfter releasedPresent slotSize slotMutable slotWellFormed
    (by rw [outerRuntime];rfl) slotStorage slotMask slotProvenance stateRace backendState stateBorrow
    (by change state.machine.user.payload.payload.user.runtime.extras.allocations.find? _ = _;rw [extrasState];exact slotExtras)
    rootFree childFree slotTree slotPointer slotAligned (by rw [outerRuntime];rfl) outerAccess ghostState shallowState destination
    (Size.ofBytes (slotBase+1)) endpoint
  let done := CanonicalCopy.replaceAllocation state slotId slotEntry.kind updated
  have trace : SuccessfulTrace.Trace config limits (Storage.withCurrent #[] caller beforeMachine) done := SuccessfulTrace.append lenTrace exitTrace
  refine ⟨done,trace,terminal,rfl,?_⟩
  exact SuccessfulTrace.no_ub ⟨config,limits,fun _ _ => True⟩ 1 _ done (by exact ⟨by decide,rfl⟩) trace (by change (0:Nat)<1;decide)
end
end DuplicatePrefix.EmptyForestPoolRejectedAfterLen

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.EmptyForestPoolRejectedAfterLen.complete) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved concrete empty rejected len-call and return dependency {dependency}"
#print axioms DuplicatePrefix.EmptyForestPoolRejectedAfterLen.complete
