import duplicate_prefix.S03EmptyLenCallReturn
namespace DuplicatePrefix.S03EmptyRootLenCall
noncomputable section
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext LenUncachedFrontend EmptyForestPoolLenCallReturn
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem with_observer
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (parentTag newTag : BorTag)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset : UInt64)
    (input : EmptyForestSharedPool.Input entry.allocation.extra parentTag newTag)
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
    (sourceLive : caller.locals[12].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 SharedReferenceMetadata.sharedLayout).imm))
    (sourceCached : caller.locals[12].layout = some SharedReferenceMetadata.sharedLayout)
    (backend : beforeMachine.user.payload.payload.user.backend = .none)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).gcInterval = 0)
    (fixed : beforeMachine.threads.fixedScheduling = true)
    (borrowRuntime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (nodeRoom : entry.allocation.extra.nodes.size+1 ≤ 4294967295)
    (ownerSource ownerSelected : Option UniIndex) (ownerMaximum : Option BorTag)
    (ownerOffset ownerLen : UInt64)
    (ownerPositive : DuplicatePrefixBorrowAuthorization.Positive entry.allocation.extra tracker.global.protectedTags
      ownerSource ownerSelected ownerMaximum ownerOffset ownerLen)
    (owner : UniIndex)
    (ownerActive : GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra owner .Write ownerOffset (ownerOffset+ownerLen))
    (zero : UniIndex) (zeroQuiet : S04ReturnReleaseInactive.Quiescent entry.allocation.extra zero) :
    ∃ finalMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser,
      (      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent #[] caller beforeMachine)
        (Storage.withCurrent #[] (resultFrame caller valid 0) finalMachine) ∧
      finalMachine.memory = releaseMemory beforeMachine.memory id entry
        (input.after)
        (input.after) ∧
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
      ∃ finalThread, finalMachine.threads.activeThread? = some finalThread) ∧
      let entryGlobal := (GeneralBorrowFnEntryRegistration.registered tracker.global {} id fresh).1
      let finalGlobal := entryGlobal.endCall (({} : FrameState).addProtector id tracker.global.nextPointerTag)
      DuplicatePrefixBorrowContract.RuntimeFacts input.after finalGlobal ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive input.after finalGlobal.protectedTags
        ownerSource ownerSelected ownerMaximum ownerOffset ownerLen) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin input.after owner .Write ownerOffset (ownerOffset+ownerLen) ∧
      S04ReturnReleaseInactive.Quiescent input.after zero := by
  let next := PtrMetadataReturn.accountedMachine options remaining span beforeMachine
  let root := cachedCaller caller valid
  have nextTracked : next.borrowTracker = some tracker := enabled
  have nextGhost : next.user.payload.ghost = false := by rw [PtrMetadataReturn.accounted_ghost];exact ghost
  have nextShallow : next.user.payload.validation = .Shallow := by rw [PtrMetadataReturn.accounted_validation];exact shallow
  have nextActive : next.threads.activeThread? = some thread := active
  have nextBackend : next.user.payload.payload.user.backend = .none := by
    unfold next PtrMetadataReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact backend
  have nextAddress : next.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩ := by
    unfold next PtrMetadataReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact cachedAddress
  let state := Storage.withCurrent #[] root next
  let destination := (LocalPlaces.localRuntimePlace 0 root 11 RootCompilerFacts.usizeLayout).stackView
  have topKnown : FrameRelevance.top (LenPush.pushed options.userRelevantCrates state destination).stack thread.topUserRelevantFrame = some 0 := by
    simp only [FrameRelevance.top,cachedThread,Option.orElse_some]
  have presentKnown : (LenPush.pushed options.userRelevantCrates state destination).stack.frames[0]? = some root := by
    simp [state,LenPush.pushed,Storage.withCurrent]
  have typeEq : (LenPush.completed options.userRelevantCrates state destination root).machine.user.payload.payload.user.types =
      beforeMachine.user.payload.payload.user.types := by
    exact LenPushFacts.types_eq options remaining span #[] root beforeMachine root
  have postMetadata : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates state destination root)).metadata = PreparedReflection.actual.runtime := by
    change (LenPush.completed options.userRelevantCrates state destination root).machine.user.payload.payload.user.types.metadata = _
    rw [typeEq]
    exact metadata
  have postNotConstructed : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates state destination root)).entries.any (·.value.ty == 4) = false := by
    change (LenPush.completed options.userRelevantCrates state destination root).machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false
    rw [typeEq]
    exact notConstructed
  exact S03EmptyLenCallReturn.with_observer options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq parentTag newTag id entry base offset input nonzero #[] caller next tracker nextTracked nextTag defaultMode fresh valid live uncached noClocks nextGhost nextShallow nextAddress present race thread 0 root nextActive topKnown presentKnown postMetadata postNotConstructed sourceBody identity callee located source sourceValid sourceLive sourceCached nextBackend beforeMachine rfl unchecked noGc fixed borrowRuntime nodeRoom ownerSource ownerSelected ownerMaximum ownerOffset ownerLen ownerPositive owner ownerActive zero zeroQuiet
end
end DuplicatePrefix.S03EmptyRootLenCall
