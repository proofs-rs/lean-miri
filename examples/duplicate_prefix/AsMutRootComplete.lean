import duplicate_prefix.AsMutCallStep
import duplicate_prefix.AsMutInitializedComplete
import duplicate_prefix.AsMutOutputMask
import duplicate_prefix.AsMutPushPreserves
namespace DuplicatePrefix.AsMutRootComplete
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess AsMutEntry AsMutCallTerminator
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
open AsMutUncachedCall
theorem run_exact
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat)
    (dispatchFuel : limits.callDispatch = budget+1)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (capacity base offset len : UInt64)
    (tree : entry.allocation.extra = tree5 tags (partitionWithInside capacity offset (offset+len) rootLocation (location5 false)))
    (allocationSize : entry.allocation.byteSize = Size.ofBytes capacity)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808) (bounds : offset.toNat+len.toNat ≤ capacity.toNat)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (mask : ProtectedStages.StageMask tags tracker.global.protectedTags 5 false)
    (nextTag : tracker.global.nextPointerTag = tags 5)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (body : caller.body = RootBody.reflected.body.body)
    (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance)
    (located : caller.location = .mir ⟨6,8⟩)
    (source : PreparedContracts.SourceComparator)
    (valid16 : (16 : MIR.LocalId) < caller.locals.size)
    (value16 : caller.locals[16].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options remaining span).access.runtime.base (Pointer.new (.concrete id (tags 4)) (Size.ofBytes (base+offset)))
      len ActualReferenceMetadata.reference).imm))
    (cached16 : caller.locals[16].layout = some ActualReferenceMetadata.reference)
    (destValid : 15 < caller.locals.size)
    (destLive : caller.locals[15].value = .live (.immediate .uninit))
    (uncached : caller.locals[15].layout = none)
    (callerClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (backend : machine.user.payload.payload.user.backend = .none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames caller machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames caller machine)).entries.any (·.value.ty == 4) = false)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller destValid) (AsMutPtrReturn.accountedMachine options remaining span machine))
      (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (topPresent : (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller destValid) (AsMutPtrReturn.accountedMachine options remaining span machine))
      (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack.frames[index]? = some current) :
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let next := AsMutPtrReturn.accountedMachine options remaining span machine
  let cached := cachedCaller caller destValid
  let before := Storage.withCurrent frames cached next
  let destination := (LocalPlaces.localRuntimePlace frames.size cached 15 CopyCompilerFacts.destPointerLayout).stackView
  let pointer : Pointer Provenance := Pointer.new (.concrete id (tags 5)) (Size.ofBytes (base+offset))
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id (tags 4)) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let post := (AsMutPush.completed options.userRelevantCrates before destination current).machine
  let finalTree := nestedTree tags (partitionWithInside capacity offset (offset+len) rootLocation (nestedLocation false))
  let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine post tracker fresh)
    (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
    memory := RetagEntry.updatedMemory post.memory id entry finalTree}
  let resultTracker := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag
  let resultEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind := {entry with allocation := entry.allocation.setExtra finalTree}
  let installed := AsMutEntry.initialized options before destination value adjusted id tracker.global.nextPointerTag
  let postThread := if (AsMutFrame.rawFrame options.userRelevantCrates (AsMutPush.fresh next).1 destination (AsMutPush.fresh next).2).extra.userRelevance >= current.extra.userRelevance
    then {thread with topUserRelevantFrame := some before.stack.frames.size} else thread
  ∃ done : CompilerFrameContext.ActualFrame,
    SuccessfulTrace.Trace cfg limits (Storage.withCurrent frames caller machine)
      (Storage.withCurrent frames
        {AsMutPtrReturn.writeFrame cached 15 (.scalar (Scalar.fromPointer cfg.access.runtime.base pointer))
          (by simpa [cached,cachedCaller,LocalPlaces.cachePlaceLayout] using destValid) with location := .mir ⟨7,0⟩}
        (AsMutPtrReturn.poppedMachine frames cached done
          (ActualPopPlan.released (AsMutPtrReturn.accountedMachine options remaining span resultMachine)
            (StackPopRelease.commitTree resultMachine.memory id resultEntry resultEntry.allocation.extra) resultTracker
            (({} : FrameState).addProtector id (tags 5)))
          (postThread.topUserRelevantFrame.getD (frames.push cached).size))) ∧
    done.extra = installed.extra := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let next := AsMutPtrReturn.accountedMachine options remaining span machine
  let cached := cachedCaller caller destValid
  let before := Storage.withCurrent frames cached next
  let destination := (LocalPlaces.localRuntimePlace frames.size cached 15 CopyCompilerFacts.destPointerLayout).stackView
  let pointer : Pointer Provenance := Pointer.new (.concrete id (tags 5)) (Size.ofBytes (base+offset))
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id (tags 4)) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let post := (AsMutPush.completed options.userRelevantCrates before destination current).machine
  let finalTree := nestedTree tags (partitionWithInside capacity offset (offset+len) rootLocation (nestedLocation false))
  let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine post tracker fresh)
    (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
    memory := RetagEntry.updatedMemory post.memory id entry finalTree}
  let resultTracker := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag
  let resultEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind := {entry with allocation := entry.allocation.setExtra finalTree}
  let installed := AsMutEntry.initialized options before destination value adjusted id tracker.global.nextPointerTag
  have first := AsMutCallStep.step options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel
    fuelEq validationEq tags distinct id entry capacity base offset len tree allocationSize positive nonzero signedFits bounds
    frames caller machine tracker enabled defaultMode mask nextTag fresh body identity callee located source valid16 value16 cached16
    destValid .uninit destLive uncached callerClocks ghost shallow cachedAddress present race backend metadata notConstructed
    unchecked noGc fixed thread index current active top topPresent
  have preserved := AsMutPushPreserves.preserves options.userRelevantCrates before destination current
  have resultPresent : resultMachine.memory.live.find? (fun row => row.1 == id) = some (id,resultEntry) :=
    MemoryCopyBridge.live_lookup_replaced post.memory id resultEntry
  have resultMask : ProtectedBorrowAccess.SixMask tags resultTracker.global.protectedTags true := by
    change ProtectedBorrowAccess.SixMask tags (tracker.global.protectedTags.insert tracker.global.nextPointerTag .StrongProtector) true
    rw [nextTag]
    exact AsMutOutputMask.inserted tags distinct tracker.global.protectedTags mask
  have resultAddress : resultMachine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ := by
    change post.user.addresses.baseAddr.find? _ = _
    rw [preserved.2.2.2.1]
    unfold before next AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact cachedAddress
  have resultGhost : resultMachine.user.payload.ghost = false := by
    change post.user.payload.ghost = false
    rw [preserved.2.2.2.2.1]
    exact (AsMutPtrReturn.accounted_ghost options remaining span machine).trans ghost
  have resultShallow : resultMachine.user.payload.validation = .Shallow := by
    change post.user.payload.validation = .Shallow
    rw [preserved.2.2.2.2.2.1]
    exact (AsMutPtrReturn.accounted_validation options remaining span machine).trans shallow
  have resultMetadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames cached resultMachine)).metadata = PreparedReflection.actual.runtime := by
    change post.user.payload.payload.user.types.metadata = _
    rw [preserved.2.2.2.2.2.2.1]
    unfold before next AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact metadata
  have resultConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames cached resultMachine)).entries.any (·.value.ty == 4) = false := by
    change post.user.payload.payload.user.types.entries.any (·.value.ty == 4) = _
    rw [preserved.2.2.2.2.2.2.1]
    unfold before next AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact notConstructed
  let postThread := if (AsMutFrame.rawFrame options.userRelevantCrates (AsMutPush.fresh next).1 destination (AsMutPush.fresh next).2).extra.userRelevance >= current.extra.userRelevance
    then {thread with topUserRelevantFrame := some before.stack.frames.size} else thread
  have resultActive : resultMachine.threads.activeThread? = some postThread :=
    AsMutPushPreserves.active_after_push (AsMutPush.fresh next).1 thread active before.stack.frames.size _ _
  have postControl : cfg.terminators.getControl post.user = cfg.terminators.getControl next.user := by
    dsimp only [post,AsMutPush.completed,Storage.withCurrent]
    rw [AsMutPushPreserves.user_after_push]
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have accountedControl : cfg.terminators.getControl next.user = TerminatorClock.advance (cfg.terminators.getControl machine.user) := by
    unfold next AsMutPtrReturn.accountedMachine SourceControl.accounted
    exact CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span _ _
  have resultUnchecked : (cfg.terminators.getControl resultMachine.user).checkedArithmetic = false := by
    change (cfg.terminators.getControl post.user).checkedArithmetic = false
    rw [postControl,accountedControl]
    exact unchecked
  have resultNoGc : (cfg.terminators.getControl resultMachine.user).gcInterval = 0 := by
    change (cfg.terminators.getControl post.user).gcInterval = 0
    rw [postControl,accountedControl]
    exact noGc
  have resultFixed : resultMachine.threads.fixedScheduling = true := preserved.2.2.2.2.2.2.2.trans fixed
  have validCached : (15 : MIR.LocalId) < cached.locals.size := by simpa [cached,cachedCaller,LocalPlaces.cachePlaceLayout] using destValid
  have liveCached : cached.locals[15].value = .live (.immediate .uninit) := by simpa [cached,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set] using destLive
  have cacheCached : cached.locals[15].layout = some CopyCompilerFacts.destPointerLayout := by simp [cached,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set_self]
  have resultSize : resultEntry.allocation.byteSize = Size.ofBytes capacity := allocationSize
  have resultTree : resultEntry.allocation.extra = finalTree := rfl
  obtain ⟨done,tail,doneExtra⟩ := AsMutInitializedComplete.run options limits remaining span debugOff validityFuel validationEq
    dynamicFuel fuelEq cmp frames cached before race value resultMachine tags distinct id resultEntry capacity base offset len
    resultPresent resultTree resultSize positive nonzero signedFits bounds resultAddress resultTracker rfl defaultMode resultMask
    resultGhost resultShallow 15 validCached liveCached cacheCached callerClocks resultMetadata resultConstructed postThread resultActive
    resultUnchecked resultNoGc resultFixed
  have first' : ExecutionMachine.step cfg limits () (Storage.withCurrent frames caller machine) =
      (Storage.withCurrent (frames.push cached) installed resultMachine,.ok true) := first
  have first'' : ExecutionMachine.step cfg limits () (Storage.withCurrent frames caller machine) =
      (Storage.withCurrent (frames.push cached)
        (AsMutEntry.initialized options before destination value
          (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base pointer len ActualReferenceMetadata.reference).imm id (tags 5)) resultMachine,.ok true) := by
    simpa only [installed,adjusted,nextTag,pointer] using first'
  refine ⟨done,SuccessfulTrace.Trace.next first'' tail,?_⟩
  simpa only [installed,adjusted,nextTag,pointer] using doneExtra

theorem run
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat)
    (dispatchFuel : limits.callDispatch = budget+1)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (capacity base offset len : UInt64)
    (tree : entry.allocation.extra = tree5 tags (partitionWithInside capacity offset (offset+len) rootLocation (location5 false)))
    (allocationSize : entry.allocation.byteSize = Size.ofBytes capacity)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808) (bounds : offset.toNat+len.toNat ≤ capacity.toNat)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (mask : ProtectedStages.StageMask tags tracker.global.protectedTags 5 false)
    (nextTag : tracker.global.nextPointerTag = tags 5)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (body : caller.body = RootBody.reflected.body.body)
    (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance)
    (located : caller.location = .mir ⟨6,8⟩)
    (source : PreparedContracts.SourceComparator)
    (valid16 : (16 : MIR.LocalId) < caller.locals.size)
    (value16 : caller.locals[16].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options remaining span).access.runtime.base (Pointer.new (.concrete id (tags 4)) (Size.ofBytes (base+offset)))
      len ActualReferenceMetadata.reference).imm))
    (cached16 : caller.locals[16].layout = some ActualReferenceMetadata.reference)
    (destValid : 15 < caller.locals.size)
    (destLive : caller.locals[15].value = .live (.immediate .uninit))
    (uncached : caller.locals[15].layout = none)
    (callerClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (backend : machine.user.payload.payload.user.backend = .none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames caller machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames caller machine)).entries.any (·.value.ty == 4) = false)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller destValid) (AsMutPtrReturn.accountedMachine options remaining span machine))
      (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (topPresent : (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller destValid) (AsMutPtrReturn.accountedMachine options remaining span machine))
      (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack.frames[index]? = some current) :
    ∃ finalFrame : CompilerFrameContext.ActualFrame, ∃ finalMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser,
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent frames caller machine) (Storage.withCurrent frames finalFrame finalMachine) ∧
      finalFrame.location = .mir ⟨7,0⟩ ∧
      finalFrame.locals[15]? = some ⟨.live (.immediate (.scalar (Scalar.fromPointer
        (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (.concrete id (tags 5)) (Size.ofBytes (base+offset)))))),some CopyCompilerFacts.destPointerLayout⟩ := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let next := AsMutPtrReturn.accountedMachine options remaining span machine
  let cached := cachedCaller caller destValid
  let before := Storage.withCurrent frames cached next
  let destination := (LocalPlaces.localRuntimePlace frames.size cached 15 CopyCompilerFacts.destPointerLayout).stackView
  let pointer : Pointer Provenance := Pointer.new (.concrete id (tags 5)) (Size.ofBytes (base+offset))
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id (tags 4)) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let post := (AsMutPush.completed options.userRelevantCrates before destination current).machine
  let finalTree := nestedTree tags (partitionWithInside capacity offset (offset+len) rootLocation (nestedLocation false))
  let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine post tracker fresh)
    (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
    memory := RetagEntry.updatedMemory post.memory id entry finalTree}
  let resultTracker := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag
  let resultEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind := {entry with allocation := entry.allocation.setExtra finalTree}
  let installed := AsMutEntry.initialized options before destination value adjusted id tracker.global.nextPointerTag
  have first := AsMutCallStep.step options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel
    fuelEq validationEq tags distinct id entry capacity base offset len tree allocationSize positive nonzero signedFits bounds
    frames caller machine tracker enabled defaultMode mask nextTag fresh body identity callee located source valid16 value16 cached16
    destValid .uninit destLive uncached callerClocks ghost shallow cachedAddress present race backend metadata notConstructed
    unchecked noGc fixed thread index current active top topPresent
  have preserved := AsMutPushPreserves.preserves options.userRelevantCrates before destination current
  have resultPresent : resultMachine.memory.live.find? (fun row => row.1 == id) = some (id,resultEntry) :=
    MemoryCopyBridge.live_lookup_replaced post.memory id resultEntry
  have resultMask : ProtectedBorrowAccess.SixMask tags resultTracker.global.protectedTags true := by
    change ProtectedBorrowAccess.SixMask tags (tracker.global.protectedTags.insert tracker.global.nextPointerTag .StrongProtector) true
    rw [nextTag]
    exact AsMutOutputMask.inserted tags distinct tracker.global.protectedTags mask
  have resultAddress : resultMachine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ := by
    change post.user.addresses.baseAddr.find? _ = _
    rw [preserved.2.2.2.1]
    unfold before next AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact cachedAddress
  have resultGhost : resultMachine.user.payload.ghost = false := by
    change post.user.payload.ghost = false
    rw [preserved.2.2.2.2.1]
    exact (AsMutPtrReturn.accounted_ghost options remaining span machine).trans ghost
  have resultShallow : resultMachine.user.payload.validation = .Shallow := by
    change post.user.payload.validation = .Shallow
    rw [preserved.2.2.2.2.2.1]
    exact (AsMutPtrReturn.accounted_validation options remaining span machine).trans shallow
  have resultMetadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames cached resultMachine)).metadata = PreparedReflection.actual.runtime := by
    change post.user.payload.payload.user.types.metadata = _
    rw [preserved.2.2.2.2.2.2.1]
    unfold before next AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact metadata
  have resultConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames cached resultMachine)).entries.any (·.value.ty == 4) = false := by
    change post.user.payload.payload.user.types.entries.any (·.value.ty == 4) = _
    rw [preserved.2.2.2.2.2.2.1]
    unfold before next AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact notConstructed
  let postThread := if (AsMutFrame.rawFrame options.userRelevantCrates (AsMutPush.fresh next).1 destination (AsMutPush.fresh next).2).extra.userRelevance >= current.extra.userRelevance
    then {thread with topUserRelevantFrame := some before.stack.frames.size} else thread
  have resultActive : resultMachine.threads.activeThread? = some postThread :=
    AsMutPushPreserves.active_after_push (AsMutPush.fresh next).1 thread active before.stack.frames.size _ _
  have postControl : cfg.terminators.getControl post.user = cfg.terminators.getControl next.user := by
    dsimp only [post,AsMutPush.completed,Storage.withCurrent]
    rw [AsMutPushPreserves.user_after_push]
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have accountedControl : cfg.terminators.getControl next.user = TerminatorClock.advance (cfg.terminators.getControl machine.user) := by
    unfold next AsMutPtrReturn.accountedMachine SourceControl.accounted
    exact CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span _ _
  have resultUnchecked : (cfg.terminators.getControl resultMachine.user).checkedArithmetic = false := by
    change (cfg.terminators.getControl post.user).checkedArithmetic = false
    rw [postControl,accountedControl]
    exact unchecked
  have resultNoGc : (cfg.terminators.getControl resultMachine.user).gcInterval = 0 := by
    change (cfg.terminators.getControl post.user).gcInterval = 0
    rw [postControl,accountedControl]
    exact noGc
  have resultFixed : resultMachine.threads.fixedScheduling = true := preserved.2.2.2.2.2.2.2.trans fixed
  have validCached : (15 : MIR.LocalId) < cached.locals.size := by simpa [cached,cachedCaller,LocalPlaces.cachePlaceLayout] using destValid
  have liveCached : cached.locals[15].value = .live (.immediate .uninit) := by simpa [cached,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set] using destLive
  have cacheCached : cached.locals[15].layout = some CopyCompilerFacts.destPointerLayout := by simp [cached,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set_self]
  have resultSize : resultEntry.allocation.byteSize = Size.ofBytes capacity := allocationSize
  have resultTree : resultEntry.allocation.extra = finalTree := rfl
  obtain ⟨done,tail,doneExtra⟩ := AsMutInitializedComplete.run options limits remaining span debugOff validityFuel validationEq
    dynamicFuel fuelEq cmp frames cached before race value resultMachine tags distinct id resultEntry capacity base offset len
    resultPresent resultTree resultSize positive nonzero signedFits bounds resultAddress resultTracker rfl defaultMode resultMask
    resultGhost resultShallow 15 validCached liveCached cacheCached callerClocks resultMetadata resultConstructed postThread resultActive
    resultUnchecked resultNoGc resultFixed
  have first' : ExecutionMachine.step cfg limits () (Storage.withCurrent frames caller machine) =
      (Storage.withCurrent (frames.push cached) installed resultMachine,.ok true) := first
  have first'' : ExecutionMachine.step cfg limits () (Storage.withCurrent frames caller machine) =
      (Storage.withCurrent (frames.push cached)
        (AsMutEntry.initialized options before destination value
          (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base pointer len ActualReferenceMetadata.reference).imm id (tags 5)) resultMachine,.ok true) := by
    simpa only [installed,adjusted,nextTag,pointer] using first'
  refine ⟨_,_,SuccessfulTrace.Trace.next first'' tail,rfl,?_⟩
  simp [AsMutPtrReturn.writeFrame,validCached,cacheCached]

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``run_exact) ++ (← collectAxioms ``run) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved root asmut complete dependency {dependency}"
end
end DuplicatePrefix.AsMutRootComplete
