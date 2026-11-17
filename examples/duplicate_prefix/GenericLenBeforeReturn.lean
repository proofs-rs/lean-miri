import duplicate_prefix.GenericLenCallStep
import duplicate_prefix.SliceLenBody
import duplicate_prefix.LenPushFacts
import duplicate_prefix.LenEntryState
import duplicate_prefix.MetadataOutputFacts
import duplicate_prefix.MetadataOutputCacheBound
namespace DuplicatePrefix.GenericLenBeforeReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess LenUncachedFrontend
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
set_option autoImplicit false in
structure ReturnFacts (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (len : UInt64) (argument : Immediate Provenance) : Prop where
  body : frame.body = LenHelper.body.body
  identity : frame.bodyIdentity = LenHelper.body.identity
  callee : frame.functionInstance = LenHelper.resolved.callee
  size : frame.locals.size = 3
  argument : frame.locals[1]? = some ⟨.live (.immediate argument),some SharedReferenceMetadata.sharedLayout⟩
  dead2 : frame.locals[2]?.map (·.value) = some .dead
  unchecked : ((config options (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false
  noGc : ((config options (remaining+1) span).terminators.getControl machine.user).gcInterval = 0
  fixed : machine.threads.fixedScheduling = true
  backend : machine.user.payload.payload.user.backend = .none
  active : ∃ thread, machine.threads.activeThread? = some thread

set_option autoImplicit false in
structure RootCache (frames : Array CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) : Prop where
  bound : frames=#[] → ∃ thread, machine.threads.activeThread?=some thread ∧
    ∀ index,thread.topUserRelevantFrame=some index → index<2

theorem before_return_full_data
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (initialTree : BorrowTree) (target : UniIndex) (exprTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (first : GeneralBorrowFreshSharedSequence.Data initialTree exprTag target offset len)
    (second : GeneralBorrowFreshSharedSequence.Data
      (GeneralBorrowFreshSharedSequence.child first tracker.global.protectedTags false).tree
      tracker.global.nextPointerTag (GeneralBorrowFreshSharedSequence.index first) offset len)
    (secondParent : second.parentTag = exprTag)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (GeneralBorrowRange.LocationOwned initialTree tracker.global.protectedTags target .Write) offset (offset+len) initialTree.locations)
    (tree : entry.allocation.extra = (GeneralBorrowFreshSharedSequence.child first tracker.global.protectedTags false).tree)
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
 :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let root := cachedCaller caller valid
    let borrowedTree := (GeneralBorrowFreshSharedSequence.child
      second tracker.global.protectedTags true).tree
    ∃ (result : CompilerFrameContext.ActualFrame) (finalMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      (SuccessfulTrace.Trace cfg limits (Storage.withCurrent frames caller beforeMachine)
        (Storage.withCurrent (frames.push root) result finalMachine) ∧
      result.location = .mir ⟨1,1⟩ ∧
      result.locals[0]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))),some RootCompilerFacts.usizeLayout⟩ ∧
      result.extra.borrowTracker = some (({} : FrameState).addProtector id tracker.global.nextPointerTag) ∧
      result.extra.dataRace = none ∧
      result.returnPlace.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size root 11 RootCompilerFacts.usizeLayout ∧
      result.returnContinuation = .goto (some 3) .Continue ∧ result.vaList = #[] ∧
      finalMachine.memory = RetagEntry.updatedMemory beforeMachine.memory id entry borrowedTree ∧
      finalMachine.borrowTracker = some (TypedBorrowSteps.registeredTracker
        (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag) ∧
      finalMachine.user.payload.ghost = false ∧ finalMachine.user.payload.validation = .Shallow ∧
      finalMachine.dataRace = none ∧
      finalMachine.user.addresses = beforeMachine.user.addresses ∧
      finalMachine.user.payload.payload.user.types = beforeMachine.user.payload.payload.user.types ∧
      finalMachine.user.payload.payload.user.runtime.extras = beforeMachine.user.payload.payload.user.runtime.extras ) ∧ ReturnFacts options remaining span result finalMachine len
        (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm ∧ RootCache frames finalMachine := by
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
  let borrowedTree := (GeneralBorrowFreshSharedSequence.child
      second tracker.global.protectedTags true).tree
  let updatedEntry := {entry with allocation := entry.allocation.setExtra borrowedTree}
  let entered := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine post tracker fresh)
    (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
    memory := RetagEntry.updatedMemory post.memory id entry borrowedTree}
  have call := GenericLenCallStep.positive_data options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq id entry base offset len initialTree target exprTag positive nonzero signedFits frames caller machine tracker enabled fresh first second secondParent owned tree allocationSize valid .uninit live uncached noClocks ghost shallow cachedAddress present race thread index current active top presentFrame metadata notConstructed sourceBody identity callee located source sourceValid sourceLive sourceCached backend beforeMachine machineEq unchecked noGc fixed
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
  have cachedPost : post.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ := by
    simp only [post,LenPush.completed,LenPush.fresh,CallEntryFacts.freshRoot,state,Storage.withCurrent,GenericPushRelevance.afterPush]
    split <;> exact cachedAddress
  have physicalBounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat := by
    rw [←allocationSize,tree]
    exact second.bounds
  have carrierValid : SliceCarrier.Valid entered
      (.inl (Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset)))) len :=
    LenEntryState.positive_carrier post tracker fresh id entry borrowedTree base offset len cachedPost positive nonzero signedFits physicalBounds
  obtain ⟨second,metadataCurrent,metadataDone,result,metadataValid,trace,rbody,ridentity,rcallee,rextra,rreturn,rcont,rva,rid,rsize,rloc,r0,r1,r2⟩ :=
    SliceLenBody.before_return options limits remaining budget dispatchFuel span debugOff validityFuel validationEq
      (frames.push root) frame entered
      (.inl (Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset)))) len carrierValid
      size (by rw [cell0]) (by rw [cell0]) (by rw [cell1];rfl) (by rw [cell1]) (by rw [cell2]) (by rw [cell2])
      control.1 control.2.1 control.2.2.1 control.2.2.2.1 frameClocks nextTracker rfl defaultMode
      pRace pBackend pGhost pValidation dynamicFuel fuelEq source cmp metadata notConstructed
      pUnchecked pNoGc pFixed nextThread pActive cacheBound
  let finalMachine := MetadataCallSummary.outputMachine options remaining span (frames.push root) second entered
    metadataValid metadataCurrent metadataDone nextThread
  refine ⟨result,finalMachine,?_,?_,?_⟩
  · refine ⟨.next entry' trace,rloc,r0,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [rextra];exact frameTracked
    · rw [rextra];exact frameClocks
    · rw [rreturn,control.2.2.2.2.1];rfl
    · rw [rcont];exact control.2.2.2.2.2.1
    · rw [rva];exact control.2.2.2.2.2.2
    · rw [MetadataOutputFacts.memory_eq]
      change RetagEntry.updatedMemory post.memory id entry borrowedTree = _
      rw [postEq,LenPushFacts.memory_eq]
    · exact MetadataOutputFacts.tracked options remaining span (frames.push root) second entered metadataValid
        metadataCurrent metadataDone nextThread nextTracker rfl
    · rw [MetadataOutputFacts.ghost_eq];exact pGhost
    · rw [MetadataOutputFacts.validation_eq];exact pValidation
    · simp only [finalMachine,MetadataCallSummary.outputMachine,PtrMetadataReturn.poppedMachine,GenericPopFrame.afterRelevanceAt]
      split
      all_goals simp only [MetadataPushFacts.posted,MetadataPush.completed,MetadataPushFacts.initial,Storage.withCurrent,GenericPushRelevance.afterPush]
      all_goals split <;> exact pRace
    · rw [MetadataOutputFacts.addresses_eq]
      change post.user.addresses = beforeMachine.user.addresses
      rw [postEq,LenPushFacts.addresses_eq]
    · rw [MetadataOutputFacts.types_eq]
      change post.user.payload.payload.user.types = beforeMachine.user.payload.payload.user.types
      rw [postEq,LenPushFacts.types_eq]
    · rw [MetadataOutputFacts.extras_eq]
      change post.user.payload.payload.user.runtime.extras = beforeMachine.user.payload.payload.user.runtime.extras
      rw [postEq,LenPushFacts.extras_eq]
  · refine ⟨rbody.trans control.1,ridentity.trans control.2.1,rcallee.trans control.2.2.1,rsize,?_,r2,?_,?_,?_,?_,?_⟩
    · rw [r1,Array.getElem?_eq_getElem valid1,cell1]
    · exact MetadataOutputFacts.unchecked options remaining span (frames.push root) second entered metadataValid
        metadataCurrent metadataDone nextThread pUnchecked
    · exact MetadataOutputFacts.no_gc options remaining span (frames.push root) second entered metadataValid
        metadataCurrent metadataDone nextThread pNoGc
    · rw [MetadataOutputFacts.fixed_eq];exact pFixed
    · rw [MetadataOutputFacts.backend_eq];exact pBackend
    · exact MetadataOutputFacts.active_exists options remaining span (frames.push root) second entered metadataValid
        metadataCurrent metadataDone nextThread pActive
  · constructor
    intro framesEmpty
    subst frames
    exact MetadataOutputCacheBound.active_cache_bounded_root options remaining span root second entered metadataValid
      metadataCurrent metadataDone nextThread pActive
      (by simpa only [Array.size_push,Array.size_empty] using cacheBound)


theorem before_return_full
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (initialTree : BorrowTree) (target : UniIndex) (exprTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (first : GeneralBorrowFreshSharedSequence.Data initialTree exprTag target offset len)
    (noFree : initialTree.tagMapping.deassigned.back? = none)
    (room : initialTree.tagMapping.mapping.size+1 ≤ 4294967295)
    (freshTag : GeneralBorrowTagMap.Fresh initialTree.tagMapping tracker.global.nextPointerTag)
    (freshProtector : GeneralBorrowProtector.Fresh initialTree tracker.global.nextPointerTag)
    (different : exprTag ≠ tracker.global.nextPointerTag)
    (cleanFuture : GeneralRangeMapState.Every
      (fun location : LocationTree => location.perms.get (GeneralBorrowFreshSharedNext.future initialTree) = none) initialTree.locations)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (GeneralBorrowRange.LocationOwned initialTree tracker.global.protectedTags target .Write) offset (offset+len) initialTree.locations)
    (tree : entry.allocation.extra = (GeneralBorrowFreshSharedSequence.child first tracker.global.protectedTags false).tree)
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
 :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let root := cachedCaller caller valid
    let borrowedTree := (GeneralBorrowFreshSharedSequence.child
      (GeneralBorrowFreshSharedNext.next initialTree tracker.global.protectedTags target exprTag tracker.global.nextPointerTag
        offset len first noFree room freshTag freshProtector different cleanFuture owned).val tracker.global.protectedTags true).tree
    ∃ (result : CompilerFrameContext.ActualFrame) (finalMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      (SuccessfulTrace.Trace cfg limits (Storage.withCurrent frames caller beforeMachine)
        (Storage.withCurrent (frames.push root) result finalMachine) ∧
      result.location = .mir ⟨1,1⟩ ∧
      result.locals[0]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))),some RootCompilerFacts.usizeLayout⟩ ∧
      result.extra.borrowTracker = some (({} : FrameState).addProtector id tracker.global.nextPointerTag) ∧
      result.extra.dataRace = none ∧
      result.returnPlace.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size root 11 RootCompilerFacts.usizeLayout ∧
      result.returnContinuation = .goto (some 3) .Continue ∧ result.vaList = #[] ∧
      finalMachine.memory = RetagEntry.updatedMemory beforeMachine.memory id entry borrowedTree ∧
      finalMachine.borrowTracker = some (TypedBorrowSteps.registeredTracker
        (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag) ∧
      finalMachine.user.payload.ghost = false ∧ finalMachine.user.payload.validation = .Shallow ∧
      finalMachine.dataRace = none ∧
      finalMachine.user.addresses = beforeMachine.user.addresses ∧
      finalMachine.user.payload.payload.user.types = beforeMachine.user.payload.payload.user.types ∧
      finalMachine.user.payload.payload.user.runtime.extras = beforeMachine.user.payload.payload.user.runtime.extras ) ∧ ReturnFacts options remaining span result finalMachine len
        (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm ∧ RootCache frames finalMachine := by
  exact before_return_full_data options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq id entry base offset len initialTree target exprTag positive nonzero signedFits frames caller machine tracker enabled defaultMode fresh first (GeneralBorrowFreshSharedNext.next initialTree tracker.global.protectedTags target exprTag tracker.global.nextPointerTag
      offset len first noFree room freshTag freshProtector different cleanFuture owned).val rfl owned tree allocationSize valid live uncached noClocks ghost shallow cachedAddress present race thread index current active top presentFrame metadata notConstructed sourceBody identity callee located source sourceValid sourceLive sourceCached backend beforeMachine machineEq unchecked noGc fixed

theorem before_return_data
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (initialTree : BorrowTree) (target : UniIndex) (exprTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (first : GeneralBorrowFreshSharedSequence.Data initialTree exprTag target offset len)
    (second : GeneralBorrowFreshSharedSequence.Data
      (GeneralBorrowFreshSharedSequence.child first tracker.global.protectedTags false).tree
      tracker.global.nextPointerTag (GeneralBorrowFreshSharedSequence.index first) offset len)
    (secondParent : second.parentTag = exprTag)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (GeneralBorrowRange.LocationOwned initialTree tracker.global.protectedTags target .Write) offset (offset+len) initialTree.locations)
    (tree : entry.allocation.extra = (GeneralBorrowFreshSharedSequence.child first tracker.global.protectedTags false).tree)
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
 :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let root := cachedCaller caller valid
    let borrowedTree := (GeneralBorrowFreshSharedSequence.child
      second tracker.global.protectedTags true).tree
    ∃ (result : CompilerFrameContext.ActualFrame) (finalMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      SuccessfulTrace.Trace cfg limits (Storage.withCurrent frames caller beforeMachine)
        (Storage.withCurrent (frames.push root) result finalMachine) ∧
      result.location = .mir ⟨1,1⟩ ∧
      result.locals[0]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))),some RootCompilerFacts.usizeLayout⟩ ∧
      result.extra.borrowTracker = some (({} : FrameState).addProtector id tracker.global.nextPointerTag) ∧
      result.extra.dataRace = none ∧
      result.returnPlace.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size root 11 RootCompilerFacts.usizeLayout ∧
      result.returnContinuation = .goto (some 3) .Continue ∧ result.vaList = #[] ∧
      finalMachine.memory = RetagEntry.updatedMemory beforeMachine.memory id entry borrowedTree ∧
      finalMachine.borrowTracker = some (TypedBorrowSteps.registeredTracker
        (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag) ∧
      finalMachine.user.payload.ghost = false ∧ finalMachine.user.payload.validation = .Shallow ∧
      finalMachine.dataRace = none ∧
      finalMachine.user.addresses = beforeMachine.user.addresses ∧
      finalMachine.user.payload.payload.user.types = beforeMachine.user.payload.payload.user.types ∧
      finalMachine.user.payload.payload.user.runtime.extras = beforeMachine.user.payload.payload.user.runtime.extras := by
  obtain ⟨result,done,properties,_,_⟩ := before_return_full_data options limits remaining budget dispatchFuel span ctx debugOff cmp
    dynamicFuel validityFuel fuelEq validationEq id entry base offset len initialTree target exprTag positive nonzero signedFits
    frames caller machine tracker enabled defaultMode fresh first second secondParent owned
    tree allocationSize valid live uncached noClocks ghost shallow cachedAddress present race thread index current active top
    presentFrame metadata notConstructed sourceBody identity callee located source sourceValid sourceLive sourceCached backend
    beforeMachine machineEq unchecked noGc fixed
  exact ⟨result,done,properties⟩


theorem before_return
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (initialTree : BorrowTree) (target : UniIndex) (exprTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (first : GeneralBorrowFreshSharedSequence.Data initialTree exprTag target offset len)
    (noFree : initialTree.tagMapping.deassigned.back? = none)
    (room : initialTree.tagMapping.mapping.size+1 ≤ 4294967295)
    (freshTag : GeneralBorrowTagMap.Fresh initialTree.tagMapping tracker.global.nextPointerTag)
    (freshProtector : GeneralBorrowProtector.Fresh initialTree tracker.global.nextPointerTag)
    (different : exprTag ≠ tracker.global.nextPointerTag)
    (cleanFuture : GeneralRangeMapState.Every
      (fun location : LocationTree => location.perms.get (GeneralBorrowFreshSharedNext.future initialTree) = none) initialTree.locations)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (GeneralBorrowRange.LocationOwned initialTree tracker.global.protectedTags target .Write) offset (offset+len) initialTree.locations)
    (tree : entry.allocation.extra = (GeneralBorrowFreshSharedSequence.child first tracker.global.protectedTags false).tree)
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
 :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let root := cachedCaller caller valid
    let borrowedTree := (GeneralBorrowFreshSharedSequence.child
      (GeneralBorrowFreshSharedNext.next initialTree tracker.global.protectedTags target exprTag tracker.global.nextPointerTag
        offset len first noFree room freshTag freshProtector different cleanFuture owned).val tracker.global.protectedTags true).tree
    ∃ (result : CompilerFrameContext.ActualFrame) (finalMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      SuccessfulTrace.Trace cfg limits (Storage.withCurrent frames caller beforeMachine)
        (Storage.withCurrent (frames.push root) result finalMachine) ∧
      result.location = .mir ⟨1,1⟩ ∧
      result.locals[0]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))),some RootCompilerFacts.usizeLayout⟩ ∧
      result.extra.borrowTracker = some (({} : FrameState).addProtector id tracker.global.nextPointerTag) ∧
      result.extra.dataRace = none ∧
      result.returnPlace.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size root 11 RootCompilerFacts.usizeLayout ∧
      result.returnContinuation = .goto (some 3) .Continue ∧ result.vaList = #[] ∧
      finalMachine.memory = RetagEntry.updatedMemory beforeMachine.memory id entry borrowedTree ∧
      finalMachine.borrowTracker = some (TypedBorrowSteps.registeredTracker
        (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag) ∧
      finalMachine.user.payload.ghost = false ∧ finalMachine.user.payload.validation = .Shallow ∧
      finalMachine.dataRace = none ∧
      finalMachine.user.addresses = beforeMachine.user.addresses ∧
      finalMachine.user.payload.payload.user.types = beforeMachine.user.payload.payload.user.types ∧
      finalMachine.user.payload.payload.user.runtime.extras = beforeMachine.user.payload.payload.user.runtime.extras := by
  exact before_return_data options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq id entry base offset len initialTree target exprTag positive nonzero signedFits frames caller machine tracker enabled defaultMode fresh first (GeneralBorrowFreshSharedNext.next initialTree tracker.global.protectedTags target exprTag tracker.global.nextPointerTag
      offset len first noFree room freshTag freshProtector different cleanFuture owned).val rfl owned tree allocationSize valid live uncached noClocks ghost shallow cachedAddress present race thread index current active top presentFrame metadata notConstructed sourceBody identity callee located source sourceValid sourceLive sourceCached backend beforeMachine machineEq unchecked noGc fixed

end
end DuplicatePrefix.GenericLenBeforeReturn
open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.GenericLenBeforeReturn.before_return,``DuplicatePrefix.GenericLenBeforeReturn.before_return_full] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved generic len before-return runtime dependency {dependency}"
