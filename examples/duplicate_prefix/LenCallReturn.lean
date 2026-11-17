import duplicate_prefix.LenCallStep
import duplicate_prefix.SliceLenComplete
import duplicate_prefix.LenPushFacts
import duplicate_prefix.LenEntryState
import duplicate_prefix.LenCallResultFrame
namespace DuplicatePrefix.LenCallReturn
noncomputable section
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess LenUncachedFrontend
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

noncomputable abbrev resultFrame := LenCallResultFrame.resultFrame

noncomputable def releaseMemory (memory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (inside afterTree : BorrowTree) :=
  StackPopRelease.commitTree (RetagEntry.updatedMemory memory id entry inside) id
    {entry with allocation := entry.allocation.setExtra inside} afterTree

theorem integer_zero
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (address : UInt64) (nonzero : address ≠ 0)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (valid : 11 < caller.locals.size)
    (live : caller.locals[11].value = .live (.immediate .uninit))
    (uncached : caller.locals[11].layout = none)
    (noClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
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
    (sourceLive : caller.locals[12].value = .live (.immediate (RetagReferencePlace.integerSliceValue address 0 SharedReferenceMetadata.sharedLayout).imm))
    (sourceCached : caller.locals[12].layout = some SharedReferenceMetadata.sharedLayout)
    (backend : machine.user.payload.payload.user.backend = .none)
    (beforeMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (machineEq : machine = PtrMetadataReturn.accountedMachine options remaining span beforeMachine)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).gcInterval = 0)
    (fixed : beforeMachine.threads.fixedScheduling = true) :
    ∃ finalMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser,
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent frames caller beforeMachine)
        (Storage.withCurrent frames (resultFrame caller valid 0) finalMachine) ∧
      finalMachine.memory = beforeMachine.memory ∧
      finalMachine.borrowTracker = some (ReferenceBorrowDriver.allocatedTracker tracker fresh) ∧
      finalMachine.user.payload.ghost = false ∧ finalMachine.user.payload.validation = .Shallow ∧
      finalMachine.dataRace = none ∧ finalMachine.threads.fixedScheduling = true ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl finalMachine.user).checkedArithmetic = false ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl finalMachine.user).gcInterval = 0 ∧
      finalMachine.user.addresses = beforeMachine.user.addresses ∧
      finalMachine.user.payload.payload.user.types = beforeMachine.user.payload.payload.user.types ∧
      finalMachine.user.payload.payload.user.backend = beforeMachine.user.payload.payload.user.backend ∧
      finalMachine.user.payload.payload.user.runtime.extras = beforeMachine.user.payload.payload.user.runtime.extras ∧
      ∃ finalThread, finalMachine.threads.activeThread? = some finalThread := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let root := cachedCaller caller valid
  let state := Storage.withCurrent frames root machine
  let destination := (LocalPlaces.localRuntimePlace frames.size root 11 RootCompilerFacts.usizeLayout).stackView
  let output := (RetagReferencePlace.integerSliceValue address 0 SharedReferenceMetadata.sharedLayout).imm
  let dummy : AllocId := ⟨1,by decide⟩
  let frame := LenEntryShape.initialized options state destination output false dummy tracker.global.nextPointerTag
  let post := (LenPush.completed options.userRelevantCrates state destination current).machine
  let nextTracker := ReferenceBorrowDriver.allocatedTracker tracker fresh
  let entered := ReferenceBorrowDriver.allocatedMachine post tracker fresh
  have entry := LenCallStep.integer_zero options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq address nonzero frames caller machine tracker enabled fresh valid .uninit live uncached noClocks ghost shallow race thread index current active top presentFrame metadata notConstructed sourceBody identity callee located source sourceValid sourceLive sourceCached backend beforeMachine machineEq unchecked noGc fixed
  have entry' : ExecutionMachine.step cfg limits () (Storage.withCurrent frames caller beforeMachine) =
      (Storage.withCurrent (frames.push root) frame entered,.ok true) := by
    simpa only [cfg,frame,LenEntryShape.initialized,state,destination,output,root,entered,post,Bool.false_eq_true,↓reduceIte] using entry
  have locals := LenEntryShape.locals options state destination output false dummy tracker.global.nextPointerTag
  have control := LenEntryShape.control options state destination output false dummy tracker.global.nextPointerTag
  have size : frame.locals.size = 3 := by change (LenEntryShape.initialized _ _ _ _ _ _ _).locals.size = 3;rw [locals];rfl
  have valid0 : 0 < frame.locals.size := by rw [size];decide
  have valid1 : 1 < frame.locals.size := by rw [size];decide
  have valid2 : 2 < frame.locals.size := by rw [size];decide
  have cell0 : frame.locals[0] = (⟨.live (.immediate .uninit),none⟩ : LocalState Provenance LocalLayout) := by
    apply Option.some.inj
    rw [←Array.getElem?_eq_getElem valid0]
    change frame.locals[0]? = _
    rw [locals]
    rfl
  have cell1 : frame.locals[1] = (⟨.live (.immediate output),some SharedReferenceMetadata.sharedLayout⟩ : LocalState Provenance LocalLayout) := by
    apply Option.some.inj
    rw [←Array.getElem?_eq_getElem valid1]
    change frame.locals[1]? = _
    rw [locals]
    rfl
  have cell2 : frame.locals[2] = (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
    apply Option.some.inj
    rw [←Array.getElem?_eq_getElem valid2]
    change frame.locals[2]? = _
    rw [locals]
    rfl
  have rootValid : 11 < root.locals.size := by simpa [root,cachedCaller,LocalPlaces.cachePlaceLayout] using valid
  have rootLive : root.locals[11].value = .live (.immediate .uninit) := by simpa [root,cachedCaller,LocalPlaces.cachePlaceLayout] using live
  have rootCached : root.locals[11].layout = some RootCompilerFacts.usizeLayout := by simp [root,cachedCaller,LocalPlaces.cachePlaceLayout]
  have frameTracked : frame.extra.borrowTracker = some ({} : FrameState) := by
    exact LenEntryShape.borrow options state destination output false dummy tracker.global.nextPointerTag tracker enabled
  have frameClocks : frame.extra.dataRace = none := LenEntryShape.no_clocks options state destination output false dummy tracker.global.nextPointerTag race
  have oldTracked : beforeMachine.borrowTracker = some tracker := by simpa only [machineEq,PtrMetadataReturn.accountedMachine,SourceControl.accounted] using enabled
  have oldActive : beforeMachine.threads.activeThread? = some thread := by simpa only [machineEq,PtrMetadataReturn.accountedMachine,SourceControl.accounted] using active
  have oldGhost : beforeMachine.user.payload.ghost = false := by
    have known := ghost
    rw [machineEq,PtrMetadataReturn.accounted_ghost] at known
    exact known
  have oldValidation : beforeMachine.user.payload.validation = .Shallow := by
    have known := shallow
    rw [machineEq,PtrMetadataReturn.accounted_validation] at known
    exact known
  have oldBackend : beforeMachine.user.payload.payload.user.backend = .none := by
    have same : machine.user.payload.payload.user.backend = beforeMachine.user.payload.payload.user.backend := by
      rw [machineEq]
      unfold PtrMetadataReturn.accountedMachine SourceControl.accounted
      rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
      rfl
    rw [←same]
    exact backend
  have postEq : post = LenPushFacts.posted options remaining span frames root beforeMachine current := by
    simp only [post,LenPushFacts.posted,LenPushFacts.initial,LenPushFacts.destination,state,destination,machineEq]
  have pGhost : entered.user.payload.ghost = false := by
    change post.user.payload.ghost = false
    rw [postEq,LenPushFacts.ghost_eq]
    exact oldGhost
  have pValidation : entered.user.payload.validation = .Shallow := by
    change post.user.payload.validation = .Shallow
    rw [postEq,LenPushFacts.validation_eq]
    exact oldValidation
  have pRace : entered.dataRace = none := by
    change post.dataRace = none
    rw [postEq,LenPushFacts.race_eq]
    simpa only [machineEq,PtrMetadataReturn.accountedMachine,SourceControl.accounted] using race
  have pBackend : entered.user.payload.payload.user.backend = .none := by
    change post.user.payload.payload.user.backend = .none
    rw [postEq,LenPushFacts.backend_eq]
    exact oldBackend
  have pFixed : entered.threads.fixedScheduling = true := by
    change post.threads.fixedScheduling = true
    rw [postEq,LenPushFacts.fixed_eq]
    exact fixed
  have pUnchecked : (cfg.terminators.getControl entered.user).checkedArithmetic = false := by
    change (cfg.terminators.getControl post.user).checkedArithmetic = false
    rw [postEq]
    exact LenPushFacts.unchecked options remaining span frames root beforeMachine current unchecked
  have pNoGc : (cfg.terminators.getControl entered.user).gcInterval = 0 := by
    change (cfg.terminators.getControl post.user).gcInterval = 0
    rw [postEq]
    exact LenPushFacts.no_gc options remaining span frames root beforeMachine current noGc
  let nextThread := PushThread.after thread (frames.size+1) (LenFrame.rank options.userRelevantCrates) current.extra.userRelevance
  have pActive : entered.threads.activeThread? = some nextThread := by
    change post.threads.activeThread? = some nextThread
    rw [postEq]
    exact LenPushFacts.active options remaining span frames root beforeMachine current thread oldActive
  have bound : index < frames.size+2 := by
    have known := (Array.getElem?_eq_some_iff.mp presentFrame).choose
    simpa only [LenPush.pushed,Storage.withCurrent,Array.size_push] using known
  have oldBound (i : Nat) (same : thread.topUserRelevantFrame = some i) : i < frames.size+2 := by
    have eq : i = index := by simpa only [FrameRelevance.top,same,Option.orElse_some,Option.some.injEq] using top
    simpa only [eq] using bound
  have cacheBound (i : Nat) (same : nextThread.topUserRelevantFrame = some i) : i < (frames.push root).size+1 := by
    simp only [Array.size_push]
    unfold nextThread PushThread.after at same
    split at same
    · have eq : frames.size+1 = i := by simpa using same
      omega
    · exact oldBound i same
  let shape : LenReleaseShape.Shape nextTracker.global.protectedTags ({} : FrameState).protectedTags entered.memory :=
    .noRows rfl
  obtain ⟨finalMachine,trace,memoryEq,trackedEq,fg,fv,fr,ff,fu,fnc,fa,ft,fb,fe,finalActive⟩ := SliceLenComplete.returns_len options limits remaining budget dispatchFuel span
    debugOff validityFuel validationEq frames root frame entered (.inr address) 0 (SliceCarrier.Valid.zeroInteger address nonzero)
    size (by rw [cell0]) (by rw [cell0]) (by rw [cell1];rfl) (by rw [cell1])
    (by rw [cell2]) (by rw [cell2])
    control.1 control.2.1 control.2.2.1 control.2.2.2.1 frameClocks nextTracker rfl defaultMode
    pRace pBackend pGhost pValidation dynamicFuel fuelEq source cmp metadata notConstructed
    pUnchecked pNoGc pFixed nextThread pActive cacheBound 11 rootValid rootLive rootCached noClocks
    (by rw [control.2.2.2.2.1];rfl) 3 .Continue control.2.2.2.2.2.1 control.2.2.2.2.2.2
    {} frameTracked shape
  refine ⟨finalMachine,?_,?_,?_,fg,fv,fr,ff,fu,fnc,?_,?_,?_,?_,finalActive⟩
  · have finalFrame : {PtrMetadataExecution.writeFrame root 11 (.scalar (.fromScalarInt (.ofUInt64 0))) rootValid with location := .mir ⟨3,0⟩} = resultFrame caller valid 0 := by
      simp [root,cachedCaller,LocalPlaces.cachePlaceLayout,PtrMetadataExecution.writeFrame,resultFrame,LenCallResultFrame.resultFrame,ActualLocalCopy.written,Array.getElem_set_self,Array.set_set]
    rw [finalFrame] at trace
    exact .next entry' trace
  · rw [memoryEq]
    change post.memory = beforeMachine.memory
    rw [postEq,LenPushFacts.memory_eq]
  · simpa only [GlobalState.endCall,FrameState.protectedTags,Array.foldl_empty] using trackedEq
  · rw [fa]
    change post.user.addresses = beforeMachine.user.addresses
    rw [postEq,LenPushFacts.addresses_eq]
  · rw [ft]
    change post.user.payload.payload.user.types = beforeMachine.user.payload.payload.user.types
    rw [postEq,LenPushFacts.types_eq]
  · rw [fb]
    change post.user.payload.payload.user.backend = beforeMachine.user.payload.payload.user.backend
    rw [postEq,LenPushFacts.backend_eq]
  · rw [fe]
    change post.user.payload.payload.user.runtime.extras = beforeMachine.user.payload.payload.user.runtime.extras
    rw [postEq,LenPushFacts.extras_eq]

theorem nonlive_zero
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (id : AllocId) (allocation : AllocationInfo)
    (capacity base offset : UInt64)
    (nonzero : base+offset ≠ 0)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (allocationInfo : machine.memory.getAllocInfo id = .ok allocation)
    (nonlive : allocation.kind ≠ .liveData)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (nextTag : tracker.global.nextPointerTag = tags 3)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (valid : 11 < caller.locals.size)
    (live : caller.locals[11].value = .live (.immediate .uninit))
    (uncached : caller.locals[11].layout = none)
    (noClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
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
      (Pointer.new (.concrete id (tags 2)) (Size.ofBytes (base+offset))) 0 SharedReferenceMetadata.sharedLayout).imm))
    (sourceCached : caller.locals[12].layout = some SharedReferenceMetadata.sharedLayout)
    (backend : machine.user.payload.payload.user.backend = .none)
    (beforeMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (machineEq : machine = PtrMetadataReturn.accountedMachine options remaining span beforeMachine)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).gcInterval = 0)
    (fixed : beforeMachine.threads.fixedScheduling = true) :
    ∃ finalMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser,
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent frames caller beforeMachine)
        (Storage.withCurrent frames (resultFrame caller valid 0) finalMachine) ∧
      finalMachine.memory = beforeMachine.memory ∧
      finalMachine.borrowTracker = some {TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
        global := (TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag).global.endCall (({} : FrameState).addProtector id tracker.global.nextPointerTag)} ∧
      finalMachine.user.payload.ghost = false ∧ finalMachine.user.payload.validation = .Shallow ∧
      finalMachine.dataRace = none ∧ finalMachine.threads.fixedScheduling = true ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl finalMachine.user).checkedArithmetic = false ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl finalMachine.user).gcInterval = 0 ∧
      finalMachine.user.addresses = beforeMachine.user.addresses ∧
      finalMachine.user.payload.payload.user.types = beforeMachine.user.payload.payload.user.types ∧
      finalMachine.user.payload.payload.user.backend = beforeMachine.user.payload.payload.user.backend ∧
      finalMachine.user.payload.payload.user.runtime.extras = beforeMachine.user.payload.payload.user.runtime.extras ∧
      ∃ finalThread, finalMachine.threads.activeThread? = some finalThread := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let root := cachedCaller caller valid
  let state := Storage.withCurrent frames root machine
  let destination := (LocalPlaces.localRuntimePlace frames.size root 11 RootCompilerFacts.usizeLayout).stackView
  let output := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 SharedReferenceMetadata.sharedLayout).imm
  let frame := LenEntryShape.initialized options state destination output true id tracker.global.nextPointerTag
  let post := (LenPush.completed options.userRelevantCrates state destination current).machine
  let nextTracker := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag
  let borrowFrame := ({} : FrameState).addProtector id tracker.global.nextPointerTag
  let entered := TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine post tracker fresh)
    (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag
  have entry := LenCallStep.nonlive_zero options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq tags distinct id allocation capacity base offset nonzero frames caller machine allocationInfo nonlive tracker enabled nextTag fresh valid .uninit live uncached noClocks ghost shallow cachedAddress race thread index current active top presentFrame metadata notConstructed sourceBody identity callee located source sourceValid sourceLive sourceCached backend beforeMachine machineEq unchecked noGc fixed
  have entry' : ExecutionMachine.step cfg limits () (Storage.withCurrent frames caller beforeMachine) =
      (Storage.withCurrent (frames.push root) frame entered,.ok true) := by
    simpa only [cfg,frame,LenEntryShape.initialized,state,destination,output,root,entered,post,Bool.false_eq_true,Bool.true_eq,↓reduceIte] using entry
  have locals := LenEntryShape.locals options state destination output true id tracker.global.nextPointerTag
  have control := LenEntryShape.control options state destination output true id tracker.global.nextPointerTag
  have size : frame.locals.size = 3 := by change (LenEntryShape.initialized _ _ _ _ _ _ _).locals.size = 3;rw [locals];rfl
  have valid0 : 0 < frame.locals.size := by rw [size];decide
  have valid1 : 1 < frame.locals.size := by rw [size];decide
  have valid2 : 2 < frame.locals.size := by rw [size];decide
  have cell0 : frame.locals[0] = (⟨.live (.immediate .uninit),none⟩ : LocalState Provenance LocalLayout) := by
    apply Option.some.inj
    rw [←Array.getElem?_eq_getElem valid0]
    change frame.locals[0]? = _
    rw [locals]
    rfl
  have cell1 : frame.locals[1] = (⟨.live (.immediate output),some SharedReferenceMetadata.sharedLayout⟩ : LocalState Provenance LocalLayout) := by
    apply Option.some.inj
    rw [←Array.getElem?_eq_getElem valid1]
    change frame.locals[1]? = _
    rw [locals]
    rfl
  have cell2 : frame.locals[2] = (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
    apply Option.some.inj
    rw [←Array.getElem?_eq_getElem valid2]
    change frame.locals[2]? = _
    rw [locals]
    rfl
  have rootValid : 11 < root.locals.size := by simpa [root,cachedCaller,LocalPlaces.cachePlaceLayout] using valid
  have rootLive : root.locals[11].value = .live (.immediate .uninit) := by simpa [root,cachedCaller,LocalPlaces.cachePlaceLayout] using live
  have rootCached : root.locals[11].layout = some RootCompilerFacts.usizeLayout := by simp [root,cachedCaller,LocalPlaces.cachePlaceLayout]
  have frameTracked : frame.extra.borrowTracker = some borrowFrame := by
    exact LenEntryShape.borrow options state destination output true id tracker.global.nextPointerTag tracker enabled
  have frameClocks : frame.extra.dataRace = none := LenEntryShape.no_clocks options state destination output true id tracker.global.nextPointerTag race
  have oldTracked : beforeMachine.borrowTracker = some tracker := by simpa only [machineEq,PtrMetadataReturn.accountedMachine,SourceControl.accounted] using enabled
  have oldActive : beforeMachine.threads.activeThread? = some thread := by simpa only [machineEq,PtrMetadataReturn.accountedMachine,SourceControl.accounted] using active
  have oldGhost : beforeMachine.user.payload.ghost = false := by
    have known := ghost
    rw [machineEq,PtrMetadataReturn.accounted_ghost] at known
    exact known
  have oldValidation : beforeMachine.user.payload.validation = .Shallow := by
    have known := shallow
    rw [machineEq,PtrMetadataReturn.accounted_validation] at known
    exact known
  have oldBackend : beforeMachine.user.payload.payload.user.backend = .none := by
    have same : machine.user.payload.payload.user.backend = beforeMachine.user.payload.payload.user.backend := by
      rw [machineEq]
      unfold PtrMetadataReturn.accountedMachine SourceControl.accounted
      rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
      rfl
    rw [←same]
    exact backend
  have postEq : post = LenPushFacts.posted options remaining span frames root beforeMachine current := by
    simp only [post,LenPushFacts.posted,LenPushFacts.initial,LenPushFacts.destination,state,destination,machineEq]
  have pGhost : entered.user.payload.ghost = false := by
    change post.user.payload.ghost = false
    rw [postEq,LenPushFacts.ghost_eq]
    exact oldGhost
  have pValidation : entered.user.payload.validation = .Shallow := by
    change post.user.payload.validation = .Shallow
    rw [postEq,LenPushFacts.validation_eq]
    exact oldValidation
  have pRace : entered.dataRace = none := by
    change post.dataRace = none
    rw [postEq,LenPushFacts.race_eq]
    simpa only [machineEq,PtrMetadataReturn.accountedMachine,SourceControl.accounted] using race
  have pBackend : entered.user.payload.payload.user.backend = .none := by
    change post.user.payload.payload.user.backend = .none
    rw [postEq,LenPushFacts.backend_eq]
    exact oldBackend
  have pFixed : entered.threads.fixedScheduling = true := by
    change post.threads.fixedScheduling = true
    rw [postEq,LenPushFacts.fixed_eq]
    exact fixed
  have pUnchecked : (cfg.terminators.getControl entered.user).checkedArithmetic = false := by
    change (cfg.terminators.getControl post.user).checkedArithmetic = false
    rw [postEq]
    exact LenPushFacts.unchecked options remaining span frames root beforeMachine current unchecked
  have pNoGc : (cfg.terminators.getControl entered.user).gcInterval = 0 := by
    change (cfg.terminators.getControl post.user).gcInterval = 0
    rw [postEq]
    exact LenPushFacts.no_gc options remaining span frames root beforeMachine current noGc
  let nextThread := PushThread.after thread (frames.size+1) (LenFrame.rank options.userRelevantCrates) current.extra.userRelevance
  have pActive : entered.threads.activeThread? = some nextThread := by
    change post.threads.activeThread? = some nextThread
    rw [postEq]
    exact LenPushFacts.active options remaining span frames root beforeMachine current thread oldActive
  have bound : index < frames.size+2 := by
    have known := (Array.getElem?_eq_some_iff.mp presentFrame).choose
    simpa only [LenPush.pushed,Storage.withCurrent,Array.size_push] using known
  have oldBound (i : Nat) (same : thread.topUserRelevantFrame = some i) : i < frames.size+2 := by
    have eq : i = index := by simpa only [FrameRelevance.top,same,Option.orElse_some,Option.some.injEq] using top
    simpa only [eq] using bound
  have cacheBound (i : Nat) (same : nextThread.topUserRelevantFrame = some i) : i < (frames.push root).size+1 := by
    simp only [Array.size_push]
    unfold nextThread PushThread.after at same
    split at same
    · have eq : frames.size+1 = i := by simpa using same
      omega
    · exact oldBound i same
  have pMemory : entered.memory = machine.memory := by
    change post.memory = machine.memory
    rw [postEq,LenPushFacts.memory_eq,machineEq]
    rfl
  have pInfo : entered.memory.getAllocInfo id = .ok allocation := by rw [pMemory];exact allocationInfo
  let shape : LenReleaseShape.Shape nextTracker.global.protectedTags borrowFrame.protectedTags entered.memory :=
    .nonlive id tracker.global.nextPointerTag allocation rfl pInfo nonlive
  obtain ⟨finalMachine,trace,memoryEq,trackedEq,fg,fv,fr,ff,fu,fnc,fa,ft,fb,fe,finalActive⟩ := SliceLenComplete.returns_len options limits remaining budget dispatchFuel span
    debugOff validityFuel validationEq frames root frame entered (.inl (Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset)))) 0
      (SliceCarrier.Valid.zeroPointer _ nonzero)
    size (by rw [cell0]) (by rw [cell0]) (by rw [cell1];rfl) (by rw [cell1])
    (by rw [cell2]) (by rw [cell2])
    control.1 control.2.1 control.2.2.1 control.2.2.2.1 frameClocks nextTracker rfl defaultMode
    pRace pBackend pGhost pValidation dynamicFuel fuelEq source cmp metadata notConstructed
    pUnchecked pNoGc pFixed nextThread pActive cacheBound 11 rootValid rootLive rootCached noClocks
    (by rw [control.2.2.2.2.1];rfl) 3 .Continue control.2.2.2.2.2.1 control.2.2.2.2.2.2
    borrowFrame frameTracked shape
  refine ⟨finalMachine,?_,?_,?_,fg,fv,fr,ff,fu,fnc,?_,?_,?_,?_,finalActive⟩
  · have finalFrame : {PtrMetadataExecution.writeFrame root 11 (.scalar (.fromScalarInt (.ofUInt64 0))) rootValid with location := .mir ⟨3,0⟩} = resultFrame caller valid 0 := by
      simp [root,cachedCaller,LocalPlaces.cachePlaceLayout,PtrMetadataExecution.writeFrame,resultFrame,LenCallResultFrame.resultFrame,ActualLocalCopy.written,Array.getElem_set_self,Array.set_set]
    rw [finalFrame] at trace
    exact .next entry' trace
  · rw [memoryEq]
    change post.memory = beforeMachine.memory
    rw [postEq,LenPushFacts.memory_eq]
  · exact trackedEq
  · rw [fa]
    change post.user.addresses = beforeMachine.user.addresses
    rw [postEq,LenPushFacts.addresses_eq]
  · rw [ft]
    change post.user.payload.payload.user.types = beforeMachine.user.payload.payload.user.types
    rw [postEq,LenPushFacts.types_eq]
  · rw [fb]
    change post.user.payload.payload.user.backend = beforeMachine.user.payload.payload.user.backend
    rw [postEq,LenPushFacts.backend_eq]
  · rw [fe]
    change post.user.payload.payload.user.runtime.extras = beforeMachine.user.payload.payload.user.runtime.extras
    rw [postEq,LenPushFacts.extras_eq]

theorem live_zero
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (capacity base offset : UInt64)
    (tree : entry.allocation.extra = tree3 tags
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes capacity) rootLocation))
    (allocationSize : entry.allocation.byteSize = Size.ofBytes capacity)
    (nonzero : base+offset ≠ 0)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (nextTag : tracker.global.nextPointerTag = tags 3)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
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
      (Pointer.new (.concrete id (tags 2)) (Size.ofBytes (base+offset))) 0 SharedReferenceMetadata.sharedLayout).imm))
    (sourceCached : caller.locals[12].layout = some SharedReferenceMetadata.sharedLayout)
    (backend : machine.user.payload.payload.user.backend = .none)
    (beforeMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (machineEq : machine = PtrMetadataReturn.accountedMachine options remaining span beforeMachine)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).gcInterval = 0)
    (fixed : beforeMachine.threads.fixedScheduling = true) :
    ∃ finalMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser,
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent frames caller beforeMachine)
        (Storage.withCurrent frames (resultFrame caller valid 0) finalMachine) ∧
      finalMachine.memory = releaseMemory beforeMachine.memory id entry (tree4 tags (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes capacity) rootLocation)) (tree4 tags (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes capacity) rootLocation)) ∧
      finalMachine.borrowTracker = some {TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
        global := (TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag).global.endCall (({} : FrameState).addProtector id tracker.global.nextPointerTag)} ∧
      finalMachine.user.payload.ghost = false ∧ finalMachine.user.payload.validation = .Shallow ∧
      finalMachine.dataRace = none ∧ finalMachine.threads.fixedScheduling = true ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl finalMachine.user).checkedArithmetic = false ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl finalMachine.user).gcInterval = 0 ∧
      finalMachine.user.addresses = beforeMachine.user.addresses ∧
      finalMachine.user.payload.payload.user.types = beforeMachine.user.payload.payload.user.types ∧
      finalMachine.user.payload.payload.user.backend = beforeMachine.user.payload.payload.user.backend ∧
      finalMachine.user.payload.payload.user.runtime.extras = beforeMachine.user.payload.payload.user.runtime.extras ∧
      ∃ finalThread, finalMachine.threads.activeThread? = some finalThread := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let root := cachedCaller caller valid
  let state := Storage.withCurrent frames root machine
  let destination := (LocalPlaces.localRuntimePlace frames.size root 11 RootCompilerFacts.usizeLayout).stackView
  let output := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 SharedReferenceMetadata.sharedLayout).imm
  let frame := LenEntryShape.initialized options state destination output true id tracker.global.nextPointerTag
  let post := (LenPush.completed options.userRelevantCrates state destination current).machine
  let nextTracker := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag
  let borrowFrame := ({} : FrameState).addProtector id tracker.global.nextPointerTag
  let initialTree := tree4 tags (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes capacity) rootLocation)
  let finalTree := tree4 tags (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes capacity) rootLocation)
  let updatedEntry := {entry with allocation := entry.allocation.setExtra initialTree}
  let entered := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine post tracker fresh)
    (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
    memory := RetagEntry.updatedMemory post.memory id entry initialTree}
  have call := LenCallStep.live_zero options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq tags distinct id entry capacity base offset tree allocationSize nonzero frames caller machine tracker enabled nextTag fresh valid .uninit live uncached noClocks ghost shallow cachedAddress present race thread index current active top presentFrame metadata notConstructed sourceBody identity callee located source sourceValid sourceLive sourceCached backend beforeMachine machineEq unchecked noGc fixed
  have entry' : ExecutionMachine.step cfg limits () (Storage.withCurrent frames caller beforeMachine) =
      (Storage.withCurrent (frames.push root) frame entered,.ok true) := by
    simpa only [cfg,frame,LenEntryShape.initialized,state,destination,output,root,entered,post,Bool.false_eq_true,Bool.true_eq,↓reduceIte] using call
  have locals := LenEntryShape.locals options state destination output true id tracker.global.nextPointerTag
  have control := LenEntryShape.control options state destination output true id tracker.global.nextPointerTag
  have size : frame.locals.size = 3 := by change (LenEntryShape.initialized _ _ _ _ _ _ _).locals.size = 3;rw [locals];rfl
  have valid0 : 0 < frame.locals.size := by rw [size];decide
  have valid1 : 1 < frame.locals.size := by rw [size];decide
  have valid2 : 2 < frame.locals.size := by rw [size];decide
  have cell0 : frame.locals[0] = (⟨.live (.immediate .uninit),none⟩ : LocalState Provenance LocalLayout) := by
    apply Option.some.inj
    rw [←Array.getElem?_eq_getElem valid0]
    change frame.locals[0]? = _
    rw [locals]
    rfl
  have cell1 : frame.locals[1] = (⟨.live (.immediate output),some SharedReferenceMetadata.sharedLayout⟩ : LocalState Provenance LocalLayout) := by
    apply Option.some.inj
    rw [←Array.getElem?_eq_getElem valid1]
    change frame.locals[1]? = _
    rw [locals]
    rfl
  have cell2 : frame.locals[2] = (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
    apply Option.some.inj
    rw [←Array.getElem?_eq_getElem valid2]
    change frame.locals[2]? = _
    rw [locals]
    rfl
  have rootValid : 11 < root.locals.size := by simpa [root,cachedCaller,LocalPlaces.cachePlaceLayout] using valid
  have rootLive : root.locals[11].value = .live (.immediate .uninit) := by simpa [root,cachedCaller,LocalPlaces.cachePlaceLayout] using live
  have rootCached : root.locals[11].layout = some RootCompilerFacts.usizeLayout := by simp [root,cachedCaller,LocalPlaces.cachePlaceLayout]
  have frameTracked : frame.extra.borrowTracker = some borrowFrame := by
    exact LenEntryShape.borrow options state destination output true id tracker.global.nextPointerTag tracker enabled
  have frameClocks : frame.extra.dataRace = none := LenEntryShape.no_clocks options state destination output true id tracker.global.nextPointerTag race
  have oldTracked : beforeMachine.borrowTracker = some tracker := by simpa only [machineEq,PtrMetadataReturn.accountedMachine,SourceControl.accounted] using enabled
  have oldActive : beforeMachine.threads.activeThread? = some thread := by simpa only [machineEq,PtrMetadataReturn.accountedMachine,SourceControl.accounted] using active
  have oldGhost : beforeMachine.user.payload.ghost = false := by
    have known := ghost
    rw [machineEq,PtrMetadataReturn.accounted_ghost] at known
    exact known
  have oldValidation : beforeMachine.user.payload.validation = .Shallow := by
    have known := shallow
    rw [machineEq,PtrMetadataReturn.accounted_validation] at known
    exact known
  have oldBackend : beforeMachine.user.payload.payload.user.backend = .none := by
    have same : machine.user.payload.payload.user.backend = beforeMachine.user.payload.payload.user.backend := by
      rw [machineEq]
      unfold PtrMetadataReturn.accountedMachine SourceControl.accounted
      rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
      rfl
    rw [←same]
    exact backend
  have postEq : post = LenPushFacts.posted options remaining span frames root beforeMachine current := by
    simp only [post,LenPushFacts.posted,LenPushFacts.initial,LenPushFacts.destination,state,destination,machineEq]
  have pGhost : entered.user.payload.ghost = false := by
    change post.user.payload.ghost = false
    rw [postEq,LenPushFacts.ghost_eq]
    exact oldGhost
  have pValidation : entered.user.payload.validation = .Shallow := by
    change post.user.payload.validation = .Shallow
    rw [postEq,LenPushFacts.validation_eq]
    exact oldValidation
  have pRace : entered.dataRace = none := by
    change post.dataRace = none
    rw [postEq,LenPushFacts.race_eq]
    simpa only [machineEq,PtrMetadataReturn.accountedMachine,SourceControl.accounted] using race
  have pBackend : entered.user.payload.payload.user.backend = .none := by
    change post.user.payload.payload.user.backend = .none
    rw [postEq,LenPushFacts.backend_eq]
    exact oldBackend
  have pFixed : entered.threads.fixedScheduling = true := by
    change post.threads.fixedScheduling = true
    rw [postEq,LenPushFacts.fixed_eq]
    exact fixed
  have pUnchecked : (cfg.terminators.getControl entered.user).checkedArithmetic = false := by
    change (cfg.terminators.getControl post.user).checkedArithmetic = false
    rw [postEq]
    exact LenPushFacts.unchecked options remaining span frames root beforeMachine current unchecked
  have pNoGc : (cfg.terminators.getControl entered.user).gcInterval = 0 := by
    change (cfg.terminators.getControl post.user).gcInterval = 0
    rw [postEq]
    exact LenPushFacts.no_gc options remaining span frames root beforeMachine current noGc
  let nextThread := PushThread.after thread (frames.size+1) (LenFrame.rank options.userRelevantCrates) current.extra.userRelevance
  have pActive : entered.threads.activeThread? = some nextThread := by
    change post.threads.activeThread? = some nextThread
    rw [postEq]
    exact LenPushFacts.active options remaining span frames root beforeMachine current thread oldActive
  have bound : index < frames.size+2 := by
    have known := (Array.getElem?_eq_some_iff.mp presentFrame).choose
    simpa only [LenPush.pushed,Storage.withCurrent,Array.size_push] using known
  have oldBound (i : Nat) (same : thread.topUserRelevantFrame = some i) : i < frames.size+2 := by
    have eq : i = index := by simpa only [FrameRelevance.top,same,Option.orElse_some,Option.some.injEq] using top
    simpa only [eq] using bound
  have cacheBound (i : Nat) (same : nextThread.topUserRelevantFrame = some i) : i < (frames.push root).size+1 := by
    simp only [Array.size_push]
    unfold nextThread PushThread.after at same
    split at same
    · have eq : frames.size+1 = i := by simpa using same
      omega
    · exact oldBound i same
  have newLookup : entered.memory.live.find? (fun row => row.1 == id) = some (id,updatedEntry) :=
    MemoryCopyBridge.live_lookup_replaced post.memory id updatedEntry
  let shape : LenReleaseShape.Shape nextTracker.global.protectedTags borrowFrame.protectedTags entered.memory :=
    .liveZero id updatedEntry tags distinct capacity
      (by simp [borrowFrame,FrameState.addProtector,nextTag]) newLookup rfl
  have carrierValid : SliceCarrier.Valid entered
      (.inl (Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset)))) 0 :=
    SliceCarrier.Valid.zeroPointer _ nonzero
  obtain ⟨finalMachine,trace,memoryEq,trackedEq,fg,fv,fr,ff,fu,fnc,fa,ft,fb,fe,finalActive⟩ := SliceLenComplete.returns_len options limits remaining budget dispatchFuel span
    debugOff validityFuel validationEq frames root frame entered (.inl (Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset)))) 0 carrierValid
    size (by rw [cell0]) (by rw [cell0]) (by rw [cell1];rfl) (by rw [cell1])
    (by rw [cell2]) (by rw [cell2])
    control.1 control.2.1 control.2.2.1 control.2.2.2.1 frameClocks nextTracker rfl defaultMode
    pRace pBackend pGhost pValidation dynamicFuel fuelEq source cmp metadata notConstructed
    pUnchecked pNoGc pFixed nextThread pActive cacheBound 11 rootValid rootLive rootCached noClocks
    (by rw [control.2.2.2.2.1];rfl) 3 .Continue control.2.2.2.2.2.1 control.2.2.2.2.2.2
    borrowFrame frameTracked shape
  refine ⟨finalMachine,?_,?_,?_,fg,fv,fr,ff,fu,fnc,?_,?_,?_,?_,finalActive⟩
  · have finalFrame : {PtrMetadataExecution.writeFrame root 11 (.scalar (.fromScalarInt (.ofUInt64 0))) rootValid with location := .mir ⟨3,0⟩} = resultFrame caller valid 0 := by
      simp [root,cachedCaller,LocalPlaces.cachePlaceLayout,PtrMetadataExecution.writeFrame,resultFrame,LenCallResultFrame.resultFrame,ActualLocalCopy.written,Array.getElem_set_self,Array.set_set]
    rw [finalFrame] at trace
    exact .next entry' trace
  · rw [memoryEq]
    change StackPopRelease.commitTree (RetagEntry.updatedMemory post.memory id entry initialTree) id updatedEntry finalTree = _
    have memorySame : post.memory = beforeMachine.memory := by rw [postEq,LenPushFacts.memory_eq]
    rw [memorySame]
    rfl
  · exact trackedEq
  · rw [fa]
    change post.user.addresses = beforeMachine.user.addresses
    rw [postEq,LenPushFacts.addresses_eq]
  · rw [ft]
    change post.user.payload.payload.user.types = beforeMachine.user.payload.payload.user.types
    rw [postEq,LenPushFacts.types_eq]
  · rw [fb]
    change post.user.payload.payload.user.backend = beforeMachine.user.payload.payload.user.backend
    rw [postEq,LenPushFacts.backend_eq]
  · rw [fe]
    change post.user.payload.payload.user.runtime.extras = beforeMachine.user.payload.payload.user.runtime.extras
    rw [postEq,LenPushFacts.extras_eq]

theorem positive
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (capacity base offset len : UInt64)
    (tree : entry.allocation.extra = tree3 tags
      (partitionWithInside capacity offset (offset+len) rootLocation (location3 false)))
    (allocationSize : entry.allocation.byteSize = Size.ofBytes capacity)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (mask : ProtectedStages.StageMask tags tracker.global.protectedTags 3 false)
    (nextTag : tracker.global.nextPointerTag = tags 3)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
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
      (Pointer.new (.concrete id (tags 2)) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm))
    (sourceCached : caller.locals[12].layout = some SharedReferenceMetadata.sharedLayout)
    (backend : machine.user.payload.payload.user.backend = .none)
    (beforeMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (machineEq : machine = PtrMetadataReturn.accountedMachine options remaining span beforeMachine)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).gcInterval = 0)
    (fixed : beforeMachine.threads.fixedScheduling = true) :
    ∃ finalMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser,
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent frames caller beforeMachine)
        (Storage.withCurrent frames (resultFrame caller valid len) finalMachine) ∧
      finalMachine.memory = releaseMemory beforeMachine.memory id entry (tree4 tags (partitionWithInside capacity offset (offset+len) rootLocation (location4 false))) (tree4 tags (partitionWithInside capacity offset (offset+len) rootLocation (location4 true))) ∧
      finalMachine.borrowTracker = some {TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
        global := (TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag).global.endCall (({} : FrameState).addProtector id tracker.global.nextPointerTag)} ∧
      finalMachine.user.payload.ghost = false ∧ finalMachine.user.payload.validation = .Shallow ∧
      finalMachine.dataRace = none ∧ finalMachine.threads.fixedScheduling = true ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl finalMachine.user).checkedArithmetic = false ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl finalMachine.user).gcInterval = 0 ∧
      finalMachine.user.addresses = beforeMachine.user.addresses ∧
      finalMachine.user.payload.payload.user.types = beforeMachine.user.payload.payload.user.types ∧
      finalMachine.user.payload.payload.user.backend = beforeMachine.user.payload.payload.user.backend ∧
      finalMachine.user.payload.payload.user.runtime.extras = beforeMachine.user.payload.payload.user.runtime.extras ∧
      ∃ finalThread, finalMachine.threads.activeThread? = some finalThread := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let root := cachedCaller caller valid
  let state := Storage.withCurrent frames root machine
  let destination := (LocalPlaces.localRuntimePlace frames.size root 11 RootCompilerFacts.usizeLayout).stackView
  let output := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
  let frame := LenEntryShape.initialized options state destination output true id tracker.global.nextPointerTag
  let post := (LenPush.completed options.userRelevantCrates state destination current).machine
  let nextTracker := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag
  let borrowFrame := ({} : FrameState).addProtector id tracker.global.nextPointerTag
  let initialTree := tree4 tags (partitionWithInside capacity offset (offset+len) rootLocation (location4 false))
  let finalTree := tree4 tags (partitionWithInside capacity offset (offset+len) rootLocation (location4 true))
  let updatedEntry := {entry with allocation := entry.allocation.setExtra initialTree}
  let entered := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine post tracker fresh)
    (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
    memory := RetagEntry.updatedMemory post.memory id entry initialTree}
  have call := LenCallStep.positive options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq tags distinct id entry capacity base offset len tree allocationSize positive nonzero signedFits bounds frames caller machine tracker enabled mask nextTag fresh valid .uninit live uncached noClocks ghost shallow cachedAddress present race thread index current active top presentFrame metadata notConstructed sourceBody identity callee located source sourceValid sourceLive sourceCached backend beforeMachine machineEq unchecked noGc fixed
  have entry' : ExecutionMachine.step cfg limits () (Storage.withCurrent frames caller beforeMachine) =
      (Storage.withCurrent (frames.push root) frame entered,.ok true) := by
    simpa only [cfg,frame,LenEntryShape.initialized,state,destination,output,root,entered,post,Bool.false_eq_true,Bool.true_eq,↓reduceIte] using call
  have locals := LenEntryShape.locals options state destination output true id tracker.global.nextPointerTag
  have control := LenEntryShape.control options state destination output true id tracker.global.nextPointerTag
  have size : frame.locals.size = 3 := by change (LenEntryShape.initialized _ _ _ _ _ _ _).locals.size = 3;rw [locals];rfl
  have valid0 : 0 < frame.locals.size := by rw [size];decide
  have valid1 : 1 < frame.locals.size := by rw [size];decide
  have valid2 : 2 < frame.locals.size := by rw [size];decide
  have cell0 : frame.locals[0] = (⟨.live (.immediate .uninit),none⟩ : LocalState Provenance LocalLayout) := by
    apply Option.some.inj
    rw [←Array.getElem?_eq_getElem valid0]
    change frame.locals[0]? = _
    rw [locals]
    rfl
  have cell1 : frame.locals[1] = (⟨.live (.immediate output),some SharedReferenceMetadata.sharedLayout⟩ : LocalState Provenance LocalLayout) := by
    apply Option.some.inj
    rw [←Array.getElem?_eq_getElem valid1]
    change frame.locals[1]? = _
    rw [locals]
    rfl
  have cell2 : frame.locals[2] = (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
    apply Option.some.inj
    rw [←Array.getElem?_eq_getElem valid2]
    change frame.locals[2]? = _
    rw [locals]
    rfl
  have rootValid : 11 < root.locals.size := by simpa [root,cachedCaller,LocalPlaces.cachePlaceLayout] using valid
  have rootLive : root.locals[11].value = .live (.immediate .uninit) := by simpa [root,cachedCaller,LocalPlaces.cachePlaceLayout] using live
  have rootCached : root.locals[11].layout = some RootCompilerFacts.usizeLayout := by simp [root,cachedCaller,LocalPlaces.cachePlaceLayout]
  have frameTracked : frame.extra.borrowTracker = some borrowFrame := by
    exact LenEntryShape.borrow options state destination output true id tracker.global.nextPointerTag tracker enabled
  have frameClocks : frame.extra.dataRace = none := LenEntryShape.no_clocks options state destination output true id tracker.global.nextPointerTag race
  have oldTracked : beforeMachine.borrowTracker = some tracker := by simpa only [machineEq,PtrMetadataReturn.accountedMachine,SourceControl.accounted] using enabled
  have oldActive : beforeMachine.threads.activeThread? = some thread := by simpa only [machineEq,PtrMetadataReturn.accountedMachine,SourceControl.accounted] using active
  have oldGhost : beforeMachine.user.payload.ghost = false := by
    have known := ghost
    rw [machineEq,PtrMetadataReturn.accounted_ghost] at known
    exact known
  have oldValidation : beforeMachine.user.payload.validation = .Shallow := by
    have known := shallow
    rw [machineEq,PtrMetadataReturn.accounted_validation] at known
    exact known
  have oldBackend : beforeMachine.user.payload.payload.user.backend = .none := by
    have same : machine.user.payload.payload.user.backend = beforeMachine.user.payload.payload.user.backend := by
      rw [machineEq]
      unfold PtrMetadataReturn.accountedMachine SourceControl.accounted
      rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
      rfl
    rw [←same]
    exact backend
  have postEq : post = LenPushFacts.posted options remaining span frames root beforeMachine current := by
    simp only [post,LenPushFacts.posted,LenPushFacts.initial,LenPushFacts.destination,state,destination,machineEq]
  have pGhost : entered.user.payload.ghost = false := by
    change post.user.payload.ghost = false
    rw [postEq,LenPushFacts.ghost_eq]
    exact oldGhost
  have pValidation : entered.user.payload.validation = .Shallow := by
    change post.user.payload.validation = .Shallow
    rw [postEq,LenPushFacts.validation_eq]
    exact oldValidation
  have pRace : entered.dataRace = none := by
    change post.dataRace = none
    rw [postEq,LenPushFacts.race_eq]
    simpa only [machineEq,PtrMetadataReturn.accountedMachine,SourceControl.accounted] using race
  have pBackend : entered.user.payload.payload.user.backend = .none := by
    change post.user.payload.payload.user.backend = .none
    rw [postEq,LenPushFacts.backend_eq]
    exact oldBackend
  have pFixed : entered.threads.fixedScheduling = true := by
    change post.threads.fixedScheduling = true
    rw [postEq,LenPushFacts.fixed_eq]
    exact fixed
  have pUnchecked : (cfg.terminators.getControl entered.user).checkedArithmetic = false := by
    change (cfg.terminators.getControl post.user).checkedArithmetic = false
    rw [postEq]
    exact LenPushFacts.unchecked options remaining span frames root beforeMachine current unchecked
  have pNoGc : (cfg.terminators.getControl entered.user).gcInterval = 0 := by
    change (cfg.terminators.getControl post.user).gcInterval = 0
    rw [postEq]
    exact LenPushFacts.no_gc options remaining span frames root beforeMachine current noGc
  let nextThread := PushThread.after thread (frames.size+1) (LenFrame.rank options.userRelevantCrates) current.extra.userRelevance
  have pActive : entered.threads.activeThread? = some nextThread := by
    change post.threads.activeThread? = some nextThread
    rw [postEq]
    exact LenPushFacts.active options remaining span frames root beforeMachine current thread oldActive
  have bound : index < frames.size+2 := by
    have known := (Array.getElem?_eq_some_iff.mp presentFrame).choose
    simpa only [LenPush.pushed,Storage.withCurrent,Array.size_push] using known
  have oldBound (i : Nat) (same : thread.topUserRelevantFrame = some i) : i < frames.size+2 := by
    have eq : i = index := by simpa only [FrameRelevance.top,same,Option.orElse_some,Option.some.injEq] using top
    simpa only [eq] using bound
  have cacheBound (i : Nat) (same : nextThread.topUserRelevantFrame = some i) : i < (frames.push root).size+1 := by
    simp only [Array.size_push]
    unfold nextThread PushThread.after at same
    split at same
    · have eq : frames.size+1 = i := by simpa using same
      omega
    · exact oldBound i same
  have newLookup : entered.memory.live.find? (fun row => row.1 == id) = some (id,updatedEntry) :=
    MemoryCopyBridge.live_lookup_replaced post.memory id updatedEntry
  have regMask : ProtectedStages.StageMask tags nextTracker.global.protectedTags 4 true :=
    LenEntryState.registered_mask tags distinct (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag nextTag mask
  let shape : LenReleaseShape.Shape nextTracker.global.protectedTags borrowFrame.protectedTags entered.memory :=
    .positive id updatedEntry tags distinct capacity offset (offset+len) false
      (by simp [borrowFrame,FrameState.addProtector,nextTag]) newLookup rfl regMask
  have cachedPost : post.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ := by
    simp only [post,LenPush.completed,LenPush.fresh,CallEntryFacts.freshRoot,state,Storage.withCurrent,GenericPushRelevance.afterPush]
    split <;> exact cachedAddress
  have carrierValid : SliceCarrier.Valid entered
      (.inl (Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset)))) len :=
    LenEntryState.positive_carrier post tracker fresh id entry initialTree base offset len cachedPost positive nonzero signedFits
      (by simpa only [allocationSize,Size.ofBytes] using bounds)
  obtain ⟨finalMachine,trace,memoryEq,trackedEq,fg,fv,fr,ff,fu,fnc,fa,ft,fb,fe,finalActive⟩ := SliceLenComplete.returns_len options limits remaining budget dispatchFuel span
    debugOff validityFuel validationEq frames root frame entered (.inl (Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset)))) len carrierValid
    size (by rw [cell0]) (by rw [cell0]) (by rw [cell1];rfl) (by rw [cell1])
    (by rw [cell2]) (by rw [cell2])
    control.1 control.2.1 control.2.2.1 control.2.2.2.1 frameClocks nextTracker rfl defaultMode
    pRace pBackend pGhost pValidation dynamicFuel fuelEq source cmp metadata notConstructed
    pUnchecked pNoGc pFixed nextThread pActive cacheBound 11 rootValid rootLive rootCached noClocks
    (by rw [control.2.2.2.2.1];rfl) 3 .Continue control.2.2.2.2.2.1 control.2.2.2.2.2.2
    borrowFrame frameTracked shape
  refine ⟨finalMachine,?_,?_,?_,fg,fv,fr,ff,fu,fnc,?_,?_,?_,?_,finalActive⟩
  · have finalFrame : {PtrMetadataExecution.writeFrame root 11 (.scalar (.fromScalarInt (.ofUInt64 len))) rootValid with location := .mir ⟨3,0⟩} = resultFrame caller valid len := by
      simp [root,cachedCaller,LocalPlaces.cachePlaceLayout,PtrMetadataExecution.writeFrame,resultFrame,LenCallResultFrame.resultFrame,ActualLocalCopy.written,Array.getElem_set_self,Array.set_set]
    rw [finalFrame] at trace
    exact .next entry' trace
  · rw [memoryEq]
    change StackPopRelease.commitTree (RetagEntry.updatedMemory post.memory id entry initialTree) id updatedEntry finalTree = _
    have memorySame : post.memory = beforeMachine.memory := by rw [postEq,LenPushFacts.memory_eq]
    rw [memorySame]
    rfl
  · exact trackedEq
  · rw [fa]
    change post.user.addresses = beforeMachine.user.addresses
    rw [postEq,LenPushFacts.addresses_eq]
  · rw [ft]
    change post.user.payload.payload.user.types = beforeMachine.user.payload.payload.user.types
    rw [postEq,LenPushFacts.types_eq]
  · rw [fb]
    change post.user.payload.payload.user.backend = beforeMachine.user.payload.payload.user.backend
    rw [postEq,LenPushFacts.backend_eq]
  · rw [fe]
    change post.user.payload.payload.user.runtime.extras = beforeMachine.user.payload.payload.user.runtime.extras
    rw [postEq,LenPushFacts.extras_eq]

open Lean Elab Command in
run_cmd do
  for declaration in [``integer_zero, ``nonlive_zero, ``live_zero, ``positive] do
   for dependency in (←collectAxioms declaration) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved full root len integer call Return {dependency}"
end
end DuplicatePrefix.LenCallReturn
