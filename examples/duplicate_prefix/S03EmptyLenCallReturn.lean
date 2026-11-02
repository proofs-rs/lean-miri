import duplicate_prefix.EmptyForestPoolLenCallReturn
import duplicate_prefix.S03EmptyLenBorrow

namespace DuplicatePrefix.S03EmptyLenCallReturn
noncomputable section
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess LenUncachedFrontend
open EmptyForestPoolLenCallReturn
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- The actual zero-length len call and return retain its caller's general
return-child capability/activity and original empty-tag quiescence. All facts
are derived from the pre-call runtime and raw allocator input. -/
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
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (nextTag : tracker.global.nextPointerTag = newTag)
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
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 SharedReferenceMetadata.sharedLayout).imm))
    (sourceCached : caller.locals[12].layout = some SharedReferenceMetadata.sharedLayout)
    (backend : machine.user.payload.payload.user.backend = .none)
    (beforeMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (machineEq : machine = PtrMetadataReturn.accountedMachine options remaining span beforeMachine)
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
        (Storage.withCurrent frames caller beforeMachine)
        (Storage.withCurrent frames (resultFrame caller valid 0) finalMachine) ∧
      finalMachine.memory = releaseMemory beforeMachine.memory id entry (input.after) (input.after) ∧
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
      ∃ finalThread, finalMachine.threads.activeThread? = some finalThread ) ∧
      let entryGlobal := (GeneralBorrowFnEntryRegistration.registered tracker.global {} id fresh).1
      let finalGlobal := entryGlobal.endCall (({} : FrameState).addProtector id tracker.global.nextPointerTag)
      DuplicatePrefixBorrowContract.RuntimeFacts input.after finalGlobal ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive input.after finalGlobal.protectedTags
        ownerSource ownerSelected ownerMaximum ownerOffset ownerLen) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin input.after owner .Write ownerOffset (ownerOffset+ownerLen) ∧
      S04ReturnReleaseInactive.Quiescent input.after zero := by
  cases nextTag
  have borrow := S03EmptyLenBorrow.with_input entry.allocation.extra tracker.global id borrowRuntime parentTag input
    nodeRoom fresh offset ownerSource ownerSelected ownerMaximum ownerOffset ownerLen ownerPositive owner ownerActive zero zeroQuiet
  obtain ⟨finalMachine,original⟩ := EmptyForestPoolLenCallReturn.live_zero
    options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    parentTag tracker.global.nextPointerTag id entry base offset input nonzero frames caller machine tracker enabled rfl
    defaultMode fresh valid live uncached noClocks ghost shallow cachedAddress present race thread index current active top presentFrame
    metadata notConstructed sourceBody identity callee located source sourceValid sourceLive sourceCached backend beforeMachine machineEq unchecked noGc fixed
  exact ⟨finalMachine,original,borrow.2.2.2.1,borrow.2.2.2.2.1,borrow.2.2.2.2.2.1,borrow.2.2.2.2.2.2⟩

end
end DuplicatePrefix.S03EmptyLenCallReturn
