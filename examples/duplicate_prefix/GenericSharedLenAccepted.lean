import duplicate_prefix.GenericSharedLenBeforeReturn
import duplicate_prefix.GeneralBorrowFreshSharedPop
import duplicate_prefix.LenReturn
import duplicate_prefix.GenericLenAcceptedPrelude
import duplicate_prefix.SingletonPlanRelease
import duplicate_prefix.GenericSharedPopPoolData
namespace DuplicatePrefix.GenericSharedLenAccepted
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext PtrMetadataExecution PtrMetadataReturn
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
set_option autoImplicit false in
structure RuntimeFacts (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) : Prop where
  ghost : after.user.payload.ghost=false
  shallow : after.user.payload.validation=.Shallow
  race : after.dataRace=none
  addresses : after.user.addresses=before.user.addresses
  types : after.user.payload.payload.user.types=before.user.payload.payload.user.types
  extras : after.user.payload.payload.user.runtime.extras=before.user.payload.payload.user.runtime.extras
  backend : after.user.payload.payload.user.backend=.none
  unchecked : ((config options (remaining+1) span).terminators.getControl after.user).checkedArithmetic=false
  noGc : ((config options (remaining+1) span).terminators.getControl after.user).gcInterval=0
  fixed : after.threads.fixedScheduling=true
  active : ∃ thread, after.threads.activeThread?=some thread ∧ thread.topUserRelevantFrame=some 0

set_option autoImplicit false in
structure EndpointFrameFacts (before after : CompilerFrameContext.ActualFrame)
    extends GenericLenAcceptedPrelude.FrameFacts before after : Prop where
  zero : after.locals[0]?=some ⟨.live (.immediate .uninit),none⟩

private theorem tick_data (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :
    let after := RootZeroCompleteState.tick options remaining span machine
    after.user.addresses=machine.user.addresses ∧
    after.user.payload.payload.user.types=machine.user.payload.payload.user.types ∧
    after.user.payload.payload.user.runtime.extras=machine.user.payload.payload.user.runtime.extras ∧
    after.user.payload.payload.user.backend=machine.user.payload.payload.user.backend := by
  unfold RootZeroCompleteState.tick SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  exact ⟨rfl,rfl,rfl,rfl⟩

private theorem tick_twice_facts (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (facts : RuntimeFacts options remaining span before machine) :
    RuntimeFacts options remaining span before (RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span machine)) := by
  have first := tick_data options remaining span machine
  have last := tick_data options remaining span (RootZeroCompleteState.tick options remaining span machine)
  exact ⟨(RootZeroCompleteState.tick_ghost options remaining span _).trans ((RootZeroCompleteState.tick_ghost options remaining span machine).trans facts.ghost),
    (RootZeroCompleteState.tick_shallow options remaining span _).trans ((RootZeroCompleteState.tick_shallow options remaining span machine).trans facts.shallow),
    facts.race,last.1.trans (first.1.trans facts.addresses),last.2.1.trans (first.2.1.trans facts.types),
    last.2.2.1.trans (first.2.2.1.trans facts.extras),last.2.2.2.trans (first.2.2.2.trans facts.backend),
    (RootZeroCompleteState.tick_flags options remaining span _).1.trans ((RootZeroCompleteState.tick_flags options remaining span machine).1.trans facts.unchecked),
    (RootZeroCompleteState.tick_flags options remaining span _).2.trans ((RootZeroCompleteState.tick_flags options remaining span machine).2.trans facts.noGc),facts.fixed,facts.active⟩

set_option autoImplicit false in
structure PreGuardFrameFacts (before after : CompilerFrameContext.ActualFrame) (len : UInt64) (value : Immediate Provenance) : Prop where
  body : after.body=before.body
  identity : after.bodyIdentity=before.bodyIdentity
  callee : after.functionInstance=before.functionInstance
  extra : after.extra=before.extra
  destination : after.returnPlace=before.returnPlace
  continuation : after.returnContinuation=before.returnContinuation
  varargs : after.vaList=before.vaList
  localsIdentity : after.localsIdentity=before.localsIdentity
  track : after.trackCallerArg=before.trackCallerArg
  size : after.locals.size=25
  location : after.location=.mir ⟨3,0⟩
  immediate : CopyHelperCleanup.AllImmediate after
  kept : ∀ i,i≠11 → i≠12 → after.locals[i]?=before.locals[i]?
  len11 : after.locals[11]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))),some RootCompilerFacts.usizeLayout⟩
  value12 : after.locals[12]?=some ⟨.live (.immediate value),some SharedReferenceMetadata.sharedLayout⟩

theorem before_guard_data
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat)
    (dispatchFuel : limits.callDispatch = budget+1) (span : PreparedContracts.FixedSpanQuery)
    (precise : options.retag.preciseInteriorMut = false) (implicitWrites : options.retag.implicitWrites = false)
    (debug : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (dynamicEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (positive : (0 : UInt64) < len) (nonnull : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (target : UniIndex)
    (first : GeneralBorrowFreshSharedSequence.Data entry.allocation.extra tracker.global.nextPointerTag target offset len)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (GeneralBorrowRange.LocationOwned entry.allocation.extra tracker.global.protectedTags target .Write)
      offset (offset+len) entry.allocation.extra.locations)
    (second : GeneralBorrowFreshSharedSequence.Data
      (GeneralBorrowFreshSharedSequence.child first tracker.global.protectedTags false).tree
      (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag
      (GeneralBorrowFreshSharedSequence.index first) offset len)
    (secondParent : second.parentTag = tracker.global.nextPointerTag)
    (roomData : entry.allocation.extra.nodes.data.size+1 ≤ 4294967295)
    (fresh2 : (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag.value < 18446744073709551615)
    (different : tracker.global.nextPointerTag ≠ (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag)
    (v1 : 1 < frame.locals.size) (v11 : 11 < frame.locals.size) (v12 : 12 < frame.locals.size)
    (sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id first.parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference)
    (lenLive : frame.locals[11].value = .live (.immediate .uninit)) (lenUncached : frame.locals[11].layout = none)
    (exprLive : frame.locals[12].value = .live (.immediate .uninit)) (exprUncached : frame.locals[12].layout = none)
    (body : frame.body = RootBody.reflected.body.body) (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) (location : frame.location = .mir ⟨2,11⟩)
    (frameRace : frame.extra.dataRace = none) (race : machine.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (backend : machine.user.payload.payload.user.backend = .none)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (threadCache : thread.topUserRelevantFrame = some 0)
    (unchecked : ((config options (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((config options (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) (source : PreparedContracts.SourceComparator)
    (rangePositive : offset.toNat < (offset+len).toNat)
    (exprUnheld : tracker.global.protectedTags.contains tracker.global.nextPointerTag = false)
    (size : frame.locals.size=25) (all : CopyHelperCleanup.AllImmediate frame)
 :
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
    ∃ (result : CompilerFrameContext.ActualFrame) (done : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (released : BorrowTree) (ended : MachineHooks.BorrowState),
      (SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] frame machine) (Storage.withCurrent #[] result done) ∧
       done.borrowTracker=some ended ∧ done.memory.live.find? (fun row => row.1 == id)=some (id,GeneralBorrowFreshSharedPop.withTree entry released) ∧
       GeneralRangeMapOrigins.OwnedOn (GeneralBorrowRange.LocationOwned released ended.global.protectedTags target .Write)
         offset (offset+len) released.locations) ∧
      (let exprTag := tracker.global.nextPointerTag
       let lenTracker := ReferenceBorrowDriver.allocatedTracker tracker fresh
       let childTag := lenTracker.global.nextPointerTag
       let childTree := (GeneralBorrowFreshSharedSequence.child second tracker.global.protectedTags true).tree
       let held := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker lenTracker fresh2) childTag
       let borrowFrame := ({} : FrameState).addProtector id childTag
       childTree.releaseProtector childTag held.global.protectedTags = ⟨released,.Released⟩ ∧
       ended = {held with global:=held.global.endCall borrowFrame}) ∧ RuntimeFacts options remaining span machine done ∧
      PreGuardFrameFacts frame result len value ∧ done.memory=RetagEntry.updatedMemory machine.memory id entry released := by
  let exprTag := tracker.global.nextPointerTag
  let lenTracker := ReferenceBorrowDriver.allocatedTracker tracker fresh
  let childTag := lenTracker.global.nextPointerTag
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id exprTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
  let exprFrame := CopyHelperSteps.advance (ActualLocalCopy.written frame 12 SharedReferenceMetadata.sharedLayout v12 value) ⟨2,11⟩
  let caller := LenUncachedFrontend.cachedCaller exprFrame
    (by simpa [exprFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using v11)
  let childTree := (GeneralBorrowFreshSharedSequence.child second tracker.global.protectedTags true).tree
  let held := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker lenTracker fresh2) childTag
  let borrowFrame := ({} : FrameState).addProtector id childTag
  obtain ⟨helper,atReturn,properties,facts,rootCache⟩ := GenericSharedLenBeforeReturn.executes_full_data options limits remaining budget dispatchFuel span
    precise implicitWrites debug cmp dynamicFuel validityFuel dynamicEq validationEq id entry base offset len positive nonnull signedFits
    frame machine tracker enabled defaultMode fresh target first capacity owned second secondParent fresh2
    v1 v11 v12 sourceLive sourceCached lenLive lenUncached exprLive exprUncached body identity callee location frameRace race ghost shallow
    cached present metadata notConstructed backend thread active threadCache unchecked noGc fixed source
  rcases properties with ⟨prefixTrace,helperLocation,retval,helperTracked,helperRace,destination,continuation,varargs,
    memoryEq,heldEq,ghostEq,shallowEq,raceEq,addressesEq,typesEq,extrasEq⟩
  let template := Storage.withCurrent #[caller] helper {atReturn with memory:=machine.memory}
  obtain ⟨pointers,table,globals,choice,retag,width,resolve,ensure,sync⟩ :=
    (CanonicalConfigFacts.actual_fields options () (remaining+1) span).retagConstruction
  have complete := GenericSharedPopPoolData.complete_data .global globals sync template held helper borrowFrame
    heldEq (by simp [template,Storage.withCurrent,Stack.currentFrame?]) helperTracked id entry present
    tracker.global.protectedTags target exprTag childTag offset len first second secondParent roomData owned
    rangePositive exprUnheld (by rfl) different (by simp [borrowFrame,FrameState.addProtector])
  obtain ⟨_,_,_,_,released,plan,pop,restored,tagAbsent⟩ := complete
  have preparedMemory : (GeneralBorrowFreshSharedPop.installed template id entry childTree).machine.memory=atReturn.memory := by
    exact memoryEq.symm
  let releasedMemory := StackPopRelease.commitTree atReturn.memory id
    (GeneralBorrowFreshSharedPop.withTree entry childTree) released
  have releasePlan : StackPopRelease.Plan held.global.protectedTags borrowFrame.protectedTags.toList atReturn.memory releasedMemory := by
    change StackPopRelease.Plan held.global.protectedTags [(id,childTag)]
      (GeneralBorrowFreshSharedPop.installed template id entry childTree).machine.memory
      (StackPopRelease.commitTree (GeneralBorrowFreshSharedPop.installed template id entry childTree).machine.memory id
        (GeneralBorrowFreshSharedPop.withTree entry childTree) released) at plan
    rw [preparedMemory] at plan
    simpa only [releasedMemory,borrowFrame,FrameState.addProtector,Array.toList_push,Array.toList_empty,List.nil_append] using plan
  have valid0 : (0 : MIR.LocalId)<helper.locals.size := by rw [facts.size];decide
  have returnedLocal : helper.locals[0]'valid0 =
      ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))),some RootCompilerFacts.usizeLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem valid0).symm.trans retval)
  have immediate : ∀ slot ∈ helper.locals, ∀ memory, slot.value ≠ .live (.indirect memory) := by
    apply PtrMetadataComplete.all_direct_three helper.locals facts.size
    · simp only [retval,Option.map_some,PtrMetadataComplete.isDirect]
    · simp only [facts.argument,Option.map_some,PtrMetadataComplete.isDirect]
    · have known := congrArg (Option.map PtrMetadataComplete.isDirect) facts.dead2
      simpa only [Option.map_map,Function.comp_def,Option.map_some,PtrMetadataComplete.isDirect] using known
  obtain ⟨returnThread,returnActive,returnBound⟩ := rootCache.bound rfl
  have callerSize : caller.locals.size=25 := by
    simp [caller,LenUncachedFrontend.cachedCaller,exprFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,size]
  have caller11 : (11 : MIR.LocalId)<caller.locals.size := by rw [callerSize];decide
  have callerLive : caller.locals[11].value= .live (.immediate .uninit) := by
    simp [caller,LenUncachedFrontend.cachedCaller,exprFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,lenLive]
  have callerCached : caller.locals[11].layout=some RootCompilerFacts.usizeLayout := by
    simp [caller,LenUncachedFrontend.cachedCaller,exprFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout]
  have callerRace : caller.extra.dataRace=none := frameRace
  have returned := LenReturn.step_with_plan options limits remaining span debug validityFuel validationEq #[] caller helper atReturn len
    facts.body helperLocation valid0 (congrArg LocalState.value returnedLocal) (congrArg LocalState.layout returnedLocal) helperRace
    11 caller11 callerLive callerCached callerRace destination 3 .Continue continuation immediate varargs held borrowFrame heldEq helperTracked
    releasedMemory releasePlan returnThread returnActive facts.unchecked facts.noGc facts.fixed ghostEq shallowEq
  let root : CompilerFrameContext.ActualFrame :=
    {writeFrame caller 11 (.scalar (.fromScalarInt (.ofUInt64 len))) caller11 with location:=.mir ⟨3,0⟩}
  let post := poppedMachine #[] caller helper
    (ActualPopPlan.released (accountedMachine options remaining span atReturn) releasedMemory held borrowFrame)
    (returnThread.topUserRelevantFrame.getD (#[].push caller).size)
  let ended := {held with global:=held.global.endCall borrowFrame}
  have step : ExecutionMachine.step (config options (remaining+1) span) limits ()
      (Storage.withCurrent #[caller] helper atReturn)=(Storage.withCurrent #[] root post,.ok true) := returned
  have returnedTrace := SuccessfulTrace.append prefixTrace (SuccessfulTrace.Trace.next step (.refl _))
  have rootSize : root.locals.size=25 := by simp [root,writeFrame,callerSize]
  have kept (i : MIR.LocalId) (valid : i<root.locals.size) (beforeValid : i<frame.locals.size)
      (n11 : i≠11) (n12 : i≠12) : root.locals[i]'valid=frame.locals[i]'beforeValid := by
    simp [root,writeFrame,caller,LenUncachedFrontend.cachedCaller,exprFrame,CopyHelperSteps.advance,
      ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,n11,n12,Ne.symm n11,Ne.symm n12]
  have rootAll : CopyHelperCleanup.AllImmediate root := by
    apply CopyHelperCleanup.all_immediate_set caller 11 _ caller11
      (CopyHelperCleanup.all_immediate_cache exprFrame 11 RootCompilerFacts.usizeLayout _
        (CopyHelperCleanup.all_immediate_written frame 12 SharedReferenceMetadata.sharedLayout value v12 all))
    intro memory;simp
  have postTracked : post.borrowTracker=some ended := by
    unfold post poppedMachine GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have postMode : ended.retagMode=.Default := defaultMode
  have postGhost : post.user.payload.ghost=false := by
    simp only [post,popped_user,ActualPopPlan.released,accounted_ghost];exact ghostEq
  have postShallow : post.user.payload.validation=.Shallow := by
    simp only [post,popped_user,ActualPopPlan.released,accounted_validation];exact shallowEq
  have postFlags :
      ((config options (remaining+1) span).terminators.getControl post.user).checkedArithmetic=false ∧
      ((config options (remaining+1) span).terminators.getControl post.user).gcInterval=0 := by
    simp only [post,popped_user,ActualPopPlan.released]
    exact ⟨(RootZeroCompleteState.tick_flags options remaining span atReturn).1.trans facts.unchecked,
      (RootZeroCompleteState.tick_flags options remaining span atReturn).2.trans facts.noGc⟩
  have postFixed : post.threads.fixedScheduling=true := by
    unfold post poppedMachine GenericPopFrame.afterRelevanceAt
    split <;> exact facts.fixed
  have postMemory : post.memory=releasedMemory := by
    unfold post poppedMachine GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have found := StackPopRelease.lookup_commit_same atReturn.memory id
    (GeneralBorrowFreshSharedPop.withTree entry childTree) released
  have nested : {(GeneralBorrowFreshSharedPop.withTree entry childTree) with allocation :=
      (GeneralBorrowFreshSharedPop.withTree entry childTree).allocation.setExtra released} =
      GeneralBorrowFreshSharedPop.withTree entry released := by
    simp [GeneralBorrowFreshSharedPop.withTree,Allocation.setExtra,Allocation.mapExtra]
  have finalFound : releasedMemory.live.find? (fun row => row.1 == id)=some (id,GeneralBorrowFreshSharedPop.withTree entry released) := by
    simpa only [releasedMemory,nested] using found
  have initialFound : atReturn.memory.live.find? (fun row => row.1 == id)=some (id,GeneralBorrowFreshSharedPop.withTree entry childTree) := by
    rw [memoryEq]
    exact StackPopRelease.lookup_commit_same machine.memory id entry childTree
  have releaseEq := SingletonPlanRelease.equation held.global.protectedTags atReturn.memory releasedMemory id childTag
    (GeneralBorrowFreshSharedPop.withTree entry childTree) (GeneralBorrowFreshSharedPop.withTree entry released)
    initialFound finalFound releasePlan
  have postData : post.user.addresses=atReturn.user.addresses ∧
      post.user.payload.payload.user.types=atReturn.user.payload.payload.user.types ∧
      post.user.payload.payload.user.runtime.extras=atReturn.user.payload.payload.user.runtime.extras ∧
      post.user.payload.payload.user.backend=atReturn.user.payload.payload.user.backend := by
    simpa only [post,popped_user,ActualPopPlan.released,RootZeroCompleteState.tick,accountedMachine] using tick_data options remaining span atReturn
  have postFacts : RuntimeFacts options remaining span machine post := by
    refine ⟨postGhost,postShallow,?_,postData.1.trans addressesEq,postData.2.1.trans typesEq,
      postData.2.2.1.trans extrasEq,postData.2.2.2.trans facts.backend,postFlags.1,postFlags.2,postFixed,?_⟩
    · unfold post poppedMachine GenericPopFrame.afterRelevanceAt
      split <;> exact raceEq
    · change ∃ thread,post.threads.activeThread?=some thread ∧ thread.topUserRelevantFrame=some 0
      let releasedMachine := ActualPopPlan.released (accountedMachine options remaining span atReturn) releasedMemory held borrowFrame
      have known : releasedMachine.threads.activeThread?=some returnThread := returnActive
      unfold post poppedMachine GenericPopFrame.afterRelevanceAt
      have pairTop : FrameRelevance.computeTop ⟨#[caller,helper]⟩ 1=some 0 := by
        simp [FrameRelevance.computeTop,List.range_succ,List.range_zero,Id.run]
        split <;> rfl
      split
      · exact ⟨_,MetadataOutputFacts.relevance_active #[caller] helper releasedMachine returnThread known,pairTop⟩
      · rename_i notCurrent
        cases cache : returnThread.topUserRelevantFrame with
        | none => simp [cache] at notCurrent
        | some index =>
          have bound := returnBound index cache
          have neq : index≠1 := by simpa [cache] using notCurrent
          have zero : index=0 := by omega
          exact ⟨returnThread,known,cache.trans (congrArg some zero)⟩
  have frameFacts : PreGuardFrameFacts frame root len value := by
    refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rootSize,rfl,rootAll,?_,?_,?_⟩
    · intro i n11 n12
      simp [root,writeFrame,caller,LenUncachedFrontend.cachedCaller,exprFrame,CopyHelperSteps.advance,
        ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem?_set,n11,n12,Ne.symm n11,Ne.symm n12]
    · simp [root,writeFrame,Array.getElem?_eq_getElem caller11,Array.getElem_set_self,callerCached]
    · simp [root,writeFrame,caller,LenUncachedFrontend.cachedCaller,exprFrame,CopyHelperSteps.advance,
        ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem?_set]
  have finalMemory : post.memory=RetagEntry.updatedMemory machine.memory id entry released := by
    rw [postMemory]
    change RetagEntry.updatedMemory atReturn.memory id (GeneralBorrowFreshSharedPop.withTree entry childTree) released=_
    rw [memoryEq]
    exact RetagEntry.updated_memory_twice machine.memory id entry childTree released
  exact ⟨root,post,released,ended,⟨returnedTrace,postTracked,by rw [postMemory];exact finalFound,restored⟩,
    ⟨releaseEq,rfl⟩,postFacts,frameFacts,finalMemory⟩

theorem before_guard
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat)
    (dispatchFuel : limits.callDispatch = budget+1) (span : PreparedContracts.FixedSpanQuery)
    (precise : options.retag.preciseInteriorMut = false) (implicitWrites : options.retag.implicitWrites = false)
    (debug : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (dynamicEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (positive : (0 : UInt64) < len) (nonnull : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (target : UniIndex)
    (first : GeneralBorrowFreshSharedSequence.Data entry.allocation.extra tracker.global.nextPointerTag target offset len)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (GeneralBorrowRange.LocationOwned entry.allocation.extra tracker.global.protectedTags target .Write)
      offset (offset+len) entry.allocation.extra.locations)
    (noFree : entry.allocation.extra.tagMapping.deassigned.back? = none)
    (room : entry.allocation.extra.tagMapping.mapping.size+1 ≤ 4294967295)
    (fresh2 : (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag.value < 18446744073709551615)
    (tagFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping
      (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag)
    (protectorFresh : GeneralBorrowProtector.Fresh entry.allocation.extra
      (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag)
    (different : tracker.global.nextPointerTag ≠ (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag)
    (cleanFuture : GeneralRangeMapState.Every (fun location : LocationTree =>
      location.perms.get (GeneralBorrowFreshSharedNext.future entry.allocation.extra) = none) entry.allocation.extra.locations)
    (v1 : 1 < frame.locals.size) (v11 : 11 < frame.locals.size) (v12 : 12 < frame.locals.size)
    (sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id first.parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference)
    (lenLive : frame.locals[11].value = .live (.immediate .uninit)) (lenUncached : frame.locals[11].layout = none)
    (exprLive : frame.locals[12].value = .live (.immediate .uninit)) (exprUncached : frame.locals[12].layout = none)
    (body : frame.body = RootBody.reflected.body.body) (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) (location : frame.location = .mir ⟨2,11⟩)
    (frameRace : frame.extra.dataRace = none) (race : machine.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (backend : machine.user.payload.payload.user.backend = .none)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (threadCache : thread.topUserRelevantFrame = some 0)
    (unchecked : ((config options (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((config options (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) (source : PreparedContracts.SourceComparator)
    (rangePositive : offset.toNat < (offset+len).toNat)
    (exprUnheld : tracker.global.protectedTags.contains tracker.global.nextPointerTag = false)
    (size : frame.locals.size=25) (all : CopyHelperCleanup.AllImmediate frame)
 :
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
    ∃ (result : CompilerFrameContext.ActualFrame) (done : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (released : BorrowTree) (ended : MachineHooks.BorrowState),
      (SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] frame machine) (Storage.withCurrent #[] result done) ∧
       done.borrowTracker=some ended ∧ done.memory.live.find? (fun row => row.1 == id)=some (id,GeneralBorrowFreshSharedPop.withTree entry released) ∧
       GeneralRangeMapOrigins.OwnedOn (GeneralBorrowRange.LocationOwned released ended.global.protectedTags target .Write)
         offset (offset+len) released.locations) ∧
      (let exprTag := tracker.global.nextPointerTag
       let lenTracker := ReferenceBorrowDriver.allocatedTracker tracker fresh
       let childTag := lenTracker.global.nextPointerTag
       let second := (GeneralBorrowFreshSharedNext.next entry.allocation.extra tracker.global.protectedTags target exprTag childTag
         offset len first noFree room tagFresh protectorFresh different cleanFuture owned).val
       let childTree := (GeneralBorrowFreshSharedSequence.child second tracker.global.protectedTags true).tree
       let held := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker lenTracker fresh2) childTag
       let borrowFrame := ({} : FrameState).addProtector id childTag
       childTree.releaseProtector childTag held.global.protectedTags = ⟨released,.Released⟩ ∧
       ended = {held with global:=held.global.endCall borrowFrame}) ∧ RuntimeFacts options remaining span machine done ∧
      PreGuardFrameFacts frame result len value ∧ done.memory=RetagEntry.updatedMemory machine.memory id entry released := by
  have aligned : entry.allocation.extra.tagMapping.mapping.size = entry.allocation.extra.nodes.data.size := by
    cases first.slot with
    | append empty aligned fits => exact aligned
    | reuse candidate available bounded vacant slack => rw [noFree] at available;cases available
  have roomData : entry.allocation.extra.nodes.data.size+1 ≤ 4294967295 := by rw [←aligned];exact room
  exact before_guard_data
    options limits remaining budget dispatchFuel span precise implicitWrites debug cmp dynamicFuel validityFuel dynamicEq validationEq
    id entry base offset len positive nonnull signedFits frame machine tracker enabled defaultMode fresh target first capacity owned
    (GeneralBorrowFreshSharedNext.next entry.allocation.extra tracker.global.protectedTags target
      tracker.global.nextPointerTag (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag
      offset len first noFree room tagFresh protectorFresh different cleanFuture owned).val rfl roomData fresh2 different v1 v11 v12 sourceLive sourceCached lenLive lenUncached exprLive exprUncached
    body identity callee location frameRace race ghost shallow cached present metadata notConstructed backend thread active threadCache
    unchecked noGc fixed source rangePositive exprUnheld size all

theorem executes_full_data
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat)
    (dispatchFuel : limits.callDispatch = budget+1) (span : PreparedContracts.FixedSpanQuery)
    (precise : options.retag.preciseInteriorMut = false) (implicitWrites : options.retag.implicitWrites = false)
    (debug : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (dynamicEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (positive : (0 : UInt64) < len) (nonnull : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (target : UniIndex)
    (first : GeneralBorrowFreshSharedSequence.Data entry.allocation.extra tracker.global.nextPointerTag target offset len)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (GeneralBorrowRange.LocationOwned entry.allocation.extra tracker.global.protectedTags target .Write)
      offset (offset+len) entry.allocation.extra.locations)
    (second : GeneralBorrowFreshSharedSequence.Data
      (GeneralBorrowFreshSharedSequence.child first tracker.global.protectedTags false).tree
      (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag
      (GeneralBorrowFreshSharedSequence.index first) offset len)
    (secondParent : second.parentTag = tracker.global.nextPointerTag)
    (roomData : entry.allocation.extra.nodes.data.size+1 ≤ 4294967295)
    (fresh2 : (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag.value < 18446744073709551615)
    (different : tracker.global.nextPointerTag ≠ (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag)
    (v1 : 1 < frame.locals.size) (v11 : 11 < frame.locals.size) (v12 : 12 < frame.locals.size)
    (sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id first.parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference)
    (lenLive : frame.locals[11].value = .live (.immediate .uninit)) (lenUncached : frame.locals[11].layout = none)
    (exprLive : frame.locals[12].value = .live (.immediate .uninit)) (exprUncached : frame.locals[12].layout = none)
    (body : frame.body = RootBody.reflected.body.body) (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) (location : frame.location = .mir ⟨2,11⟩)
    (frameRace : frame.extra.dataRace = none) (race : machine.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (backend : machine.user.payload.payload.user.backend = .none)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (threadCache : thread.topUserRelevantFrame = some 0)
    (unchecked : ((config options (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((config options (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) (source : PreparedContracts.SourceComparator)
    (rangePositive : offset.toNat < (offset+len).toNat)
    (exprUnheld : tracker.global.protectedTags.contains tracker.global.nextPointerTag = false)
    (size : frame.locals.size=25)
    (count : UInt64) (countPositive : (0 : UInt64)<count) (within : count≤len/2)
    (all : CopyHelperCleanup.AllImmediate frame)
    (live0 : (frame.locals[0]'(by omega)).value=.live (.immediate .uninit)) (cache0 : (frame.locals[0]'(by omega)).layout=none)
    (live7 : (frame.locals[7]'(by omega)).value=.live (.immediate .uninit)) (cache7 : (frame.locals[7]'(by omega)).layout=none)
    (live8 : (frame.locals[8]'(by omega)).value=.live (.immediate .uninit)) (cache8 : (frame.locals[8]'(by omega)).layout=none)
    (live9 : (frame.locals[9]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cache9 : (frame.locals[9]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (live10 : (frame.locals[10]'(by omega)).value=.live (.immediate .uninit)) (cache10 : (frame.locals[10]'(by omega)).layout=none)
    (live13 : (frame.locals[13]'(by omega)).value=.live (.immediate .uninit)) (cache13 : (frame.locals[13]'(by omega)).layout=none)
    (dead15 : (frame.locals[15]'(by omega)).value=.dead) (cache15 : (frame.locals[15]'(by omega)).layout=none)
    (dead16 : (frame.locals[16]'(by omega)).value=.dead) (cache16 : (frame.locals[16]'(by omega)).layout=none)
 :
    ∃ (result : CompilerFrameContext.ActualFrame) (done : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (released : BorrowTree) (ended : MachineHooks.BorrowState),
      (SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] frame machine) (Storage.withCurrent #[] result done) ∧
      result.location = .mir ⟨6,7⟩ ∧ done.borrowTracker=some ended ∧
      done.memory.live.find? (fun row => row.1 == id) = some (id,GeneralBorrowFreshSharedPop.withTree entry released) ∧
      result.body=frame.body ∧ result.bodyIdentity=frame.bodyIdentity ∧ result.functionInstance=frame.functionInstance ∧
      result.extra=frame.extra ∧ result.locals.size=25 ∧ result.locals[1]?=frame.locals[1]? ∧ result.locals[2]?=frame.locals[2]? ∧
      result.locals[15]?=some ⟨.live (.immediate .uninit),none⟩ ∧ result.locals[16]?=some ⟨.live (.immediate .uninit),none⟩ ∧
      CopyHelperCleanup.AllImmediate result ∧
      GeneralRangeMapOrigins.OwnedOn (GeneralBorrowRange.LocationOwned released ended.global.protectedTags target .Write)
        offset (offset+len) released.locations) ∧
      (let exprTag := tracker.global.nextPointerTag
       let lenTracker := ReferenceBorrowDriver.allocatedTracker tracker fresh
       let childTag := lenTracker.global.nextPointerTag
       let childTree := (GeneralBorrowFreshSharedSequence.child second tracker.global.protectedTags true).tree
       let held := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker lenTracker fresh2) childTag
       let borrowFrame := ({} : FrameState).addProtector id childTag
       childTree.releaseProtector childTag held.global.protectedTags = ⟨released,.Released⟩ ∧
       ended = {held with global:=held.global.endCall borrowFrame}) ∧ RuntimeFacts options remaining span machine done ∧ result.trackCallerArg=frame.trackCallerArg ∧
      EndpointFrameFacts frame result ∧ done.memory=RetagEntry.updatedMemory machine.memory id entry released := by
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
  obtain ⟨root,post,released,ended,⟨returnedTrace,tracked,found,restored⟩,releaseFacts,runtime,facts,memoryEq⟩ := before_guard_data
    options limits remaining budget dispatchFuel span precise implicitWrites debug cmp dynamicFuel validityFuel dynamicEq validationEq
    id entry base offset len positive nonnull signedFits frame machine tracker enabled defaultMode fresh target first capacity owned second secondParent roomData
    fresh2 different v1 v11 v12 sourceLive sourceCached lenLive lenUncached exprLive exprUncached
    body identity callee location frameRace race ghost shallow cached present metadata notConstructed backend thread active threadCache
    unchecked noGc fixed source rangePositive exprUnheld size all
  have valid (i : Fin 25) : i.val<root.locals.size := by rw [facts.size];exact i.isLt
  have oldValid (i : Fin 25) : i.val<frame.locals.size := by rw [size];exact i.isLt
  have kept (i : Fin 25) (n11 : i.val≠11) (n12 : i.val≠12) :
      root.locals[i.val]'(valid i)=frame.locals[i.val]'(oldValid i) :=
    Option.some.inj ((Array.getElem?_eq_getElem (valid i)).symm.trans
      ((facts.kept i.val n11 n12).trans (Array.getElem?_eq_getElem (oldValid i))))
  have keptValue (i : Fin 25) (n11 : i.val≠11) (n12 : i.val≠12) := congrArg LocalState.value (kept i n11 n12)
  have keptLayout (i : Fin 25) (n11 : i.val≠11) (n12 : i.val≠12) := congrArg LocalState.layout (kept i n11 n12)
  have eleven := Option.some.inj ((Array.getElem?_eq_getElem (valid ⟨11,by decide⟩)).symm.trans facts.len11)
  have twelve := Option.some.inj ((Array.getElem?_eq_getElem (valid ⟨12,by decide⟩)).symm.trans facts.value12)
  obtain ⟨result,guardProperties,guardFacts⟩ := GenericLenAcceptedPrelude.executes_full
    options limits remaining span source debug validityFuel validationEq root post len count countPositive within facts.size value
    (congrArg LocalState.value twelve)
    ((keptValue ⟨13,by decide⟩ (by decide) (by decide)).trans live13)
    ((keptLayout ⟨13,by decide⟩ (by decide) (by decide)).trans cache13)
    ((keptValue ⟨0,by decide⟩ (by decide) (by decide)).trans live0)
    ((keptLayout ⟨0,by decide⟩ (by decide) (by decide)).trans cache0)
    ((keptValue ⟨7,by decide⟩ (by decide) (by decide)).trans live7)
    ((keptLayout ⟨7,by decide⟩ (by decide) (by decide)).trans cache7)
    ((keptValue ⟨15,by decide⟩ (by decide) (by decide)).trans dead15)
    ((keptLayout ⟨15,by decide⟩ (by decide) (by decide)).trans cache15)
    ((keptValue ⟨16,by decide⟩ (by decide) (by decide)).trans dead16)
    ((keptLayout ⟨16,by decide⟩ (by decide) (by decide)).trans cache16)
    ((keptValue ⟨8,by decide⟩ (by decide) (by decide)).trans live8)
    ((keptLayout ⟨8,by decide⟩ (by decide) (by decide)).trans cache8)
    ((keptValue ⟨9,by decide⟩ (by decide) (by decide)).trans live9)
    ((keptLayout ⟨9,by decide⟩ (by decide) (by decide)).trans cache9)
    ((keptValue ⟨10,by decide⟩ (by decide) (by decide)).trans live10)
    ((keptLayout ⟨10,by decide⟩ (by decide) (by decide)).trans cache10)
    (congrArg LocalState.value eleven) (congrArg LocalState.layout eleven)
    (facts.body.trans body) (facts.identity.trans identity) (facts.callee.trans callee) facts.location facts.immediate
    (facts.extra ▸ frameRace) ended tracked (by rw [releaseFacts.2];exact defaultMode)
    runtime.ghost runtime.shallow runtime.unchecked runtime.noGc runtime.fixed
  rcases guardProperties with ⟨guardTrace,rbody,ridentity,rcallee,rextra,rreturn,rcont,rva,rlocal,rtrack,rsize,resultLocation,r1,r2,r15,r16,rall⟩
  have zeroBefore : frame.locals[0]?=some ⟨.live (.immediate .uninit),none⟩ := by
    rw [Array.getElem?_eq_getElem (by rw [size];decide)]
    exact congrArg some (by rw [←live0,←cache0])
  have endpoint : EndpointFrameFacts frame result := by
    refine ⟨⟨guardFacts.destination.trans facts.destination,guardFacts.continuation.trans facts.continuation,
      guardFacts.varargs.trans facts.varargs,guardFacts.slot0.trans (facts.kept 0 (by decide) (by decide)),guardFacts.slot13,?_⟩,
      guardFacts.slot0.trans ((facts.kept 0 (by decide) (by decide)).trans zeroBefore)⟩
    intro i high
    exact (guardFacts.high i high).trans (facts.kept i (by omega) (by omega))
  refine ⟨result,_,released,ended,?_,releaseFacts,tick_twice_facts options remaining span machine post runtime,
    rtrack.trans facts.track,endpoint,memoryEq⟩
  exact ⟨SuccessfulTrace.append returnedTrace guardTrace,resultLocation,tracked,found,rbody.trans facts.body,
    ridentity.trans facts.identity,rcallee.trans facts.callee,rextra.trans facts.extra,rsize,
    r1.trans (facts.kept 1 (by decide) (by decide)),r2.trans (facts.kept 2 (by decide) (by decide)),r15,r16,rall,restored⟩

theorem executes_full
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat)
    (dispatchFuel : limits.callDispatch = budget+1) (span : PreparedContracts.FixedSpanQuery)
    (precise : options.retag.preciseInteriorMut = false) (implicitWrites : options.retag.implicitWrites = false)
    (debug : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (dynamicEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (positive : (0 : UInt64) < len) (nonnull : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (target : UniIndex)
    (first : GeneralBorrowFreshSharedSequence.Data entry.allocation.extra tracker.global.nextPointerTag target offset len)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (GeneralBorrowRange.LocationOwned entry.allocation.extra tracker.global.protectedTags target .Write)
      offset (offset+len) entry.allocation.extra.locations)
    (noFree : entry.allocation.extra.tagMapping.deassigned.back? = none)
    (room : entry.allocation.extra.tagMapping.mapping.size+1 ≤ 4294967295)
    (fresh2 : (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag.value < 18446744073709551615)
    (tagFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping
      (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag)
    (protectorFresh : GeneralBorrowProtector.Fresh entry.allocation.extra
      (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag)
    (different : tracker.global.nextPointerTag ≠ (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag)
    (cleanFuture : GeneralRangeMapState.Every (fun location : LocationTree =>
      location.perms.get (GeneralBorrowFreshSharedNext.future entry.allocation.extra) = none) entry.allocation.extra.locations)
    (v1 : 1 < frame.locals.size) (v11 : 11 < frame.locals.size) (v12 : 12 < frame.locals.size)
    (sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id first.parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference)
    (lenLive : frame.locals[11].value = .live (.immediate .uninit)) (lenUncached : frame.locals[11].layout = none)
    (exprLive : frame.locals[12].value = .live (.immediate .uninit)) (exprUncached : frame.locals[12].layout = none)
    (body : frame.body = RootBody.reflected.body.body) (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) (location : frame.location = .mir ⟨2,11⟩)
    (frameRace : frame.extra.dataRace = none) (race : machine.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (backend : machine.user.payload.payload.user.backend = .none)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (threadCache : thread.topUserRelevantFrame = some 0)
    (unchecked : ((config options (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((config options (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) (source : PreparedContracts.SourceComparator)
    (rangePositive : offset.toNat < (offset+len).toNat)
    (exprUnheld : tracker.global.protectedTags.contains tracker.global.nextPointerTag = false)
    (size : frame.locals.size=25)
    (count : UInt64) (countPositive : (0 : UInt64)<count) (within : count≤len/2)
    (all : CopyHelperCleanup.AllImmediate frame)
    (live0 : (frame.locals[0]'(by omega)).value=.live (.immediate .uninit)) (cache0 : (frame.locals[0]'(by omega)).layout=none)
    (live7 : (frame.locals[7]'(by omega)).value=.live (.immediate .uninit)) (cache7 : (frame.locals[7]'(by omega)).layout=none)
    (live8 : (frame.locals[8]'(by omega)).value=.live (.immediate .uninit)) (cache8 : (frame.locals[8]'(by omega)).layout=none)
    (live9 : (frame.locals[9]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cache9 : (frame.locals[9]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (live10 : (frame.locals[10]'(by omega)).value=.live (.immediate .uninit)) (cache10 : (frame.locals[10]'(by omega)).layout=none)
    (live13 : (frame.locals[13]'(by omega)).value=.live (.immediate .uninit)) (cache13 : (frame.locals[13]'(by omega)).layout=none)
    (dead15 : (frame.locals[15]'(by omega)).value=.dead) (cache15 : (frame.locals[15]'(by omega)).layout=none)
    (dead16 : (frame.locals[16]'(by omega)).value=.dead) (cache16 : (frame.locals[16]'(by omega)).layout=none)
 :
    ∃ (result : CompilerFrameContext.ActualFrame) (done : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (released : BorrowTree) (ended : MachineHooks.BorrowState),
      (SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] frame machine) (Storage.withCurrent #[] result done) ∧
      result.location = .mir ⟨6,7⟩ ∧ done.borrowTracker=some ended ∧
      done.memory.live.find? (fun row => row.1 == id) = some (id,GeneralBorrowFreshSharedPop.withTree entry released) ∧
      result.body=frame.body ∧ result.bodyIdentity=frame.bodyIdentity ∧ result.functionInstance=frame.functionInstance ∧
      result.extra=frame.extra ∧ result.locals.size=25 ∧ result.locals[1]?=frame.locals[1]? ∧ result.locals[2]?=frame.locals[2]? ∧
      result.locals[15]?=some ⟨.live (.immediate .uninit),none⟩ ∧ result.locals[16]?=some ⟨.live (.immediate .uninit),none⟩ ∧
      CopyHelperCleanup.AllImmediate result ∧
      GeneralRangeMapOrigins.OwnedOn (GeneralBorrowRange.LocationOwned released ended.global.protectedTags target .Write)
        offset (offset+len) released.locations) ∧
      (let exprTag := tracker.global.nextPointerTag
       let lenTracker := ReferenceBorrowDriver.allocatedTracker tracker fresh
       let childTag := lenTracker.global.nextPointerTag
       let second := (GeneralBorrowFreshSharedNext.next entry.allocation.extra tracker.global.protectedTags target exprTag childTag
         offset len first noFree room tagFresh protectorFresh different cleanFuture owned).val
       let childTree := (GeneralBorrowFreshSharedSequence.child second tracker.global.protectedTags true).tree
       let held := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker lenTracker fresh2) childTag
       let borrowFrame := ({} : FrameState).addProtector id childTag
       childTree.releaseProtector childTag held.global.protectedTags = ⟨released,.Released⟩ ∧
       ended = {held with global:=held.global.endCall borrowFrame}) ∧ RuntimeFacts options remaining span machine done ∧ result.trackCallerArg=frame.trackCallerArg ∧
      EndpointFrameFacts frame result ∧ done.memory=RetagEntry.updatedMemory machine.memory id entry released := by
  have aligned : entry.allocation.extra.tagMapping.mapping.size = entry.allocation.extra.nodes.data.size := by
    cases first.slot with
    | append empty aligned fits => exact aligned
    | reuse candidate available bounded vacant slack => rw [noFree] at available;cases available
  have roomData : entry.allocation.extra.nodes.data.size+1 ≤ 4294967295 := by rw [←aligned];exact room
  exact executes_full_data options limits remaining budget dispatchFuel span precise implicitWrites debug cmp dynamicFuel validityFuel dynamicEq validationEq
    id entry base offset len positive nonnull signedFits frame machine tracker enabled defaultMode fresh target first capacity owned
    (GeneralBorrowFreshSharedNext.next entry.allocation.extra tracker.global.protectedTags target
      tracker.global.nextPointerTag (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag
      offset len first noFree room tagFresh protectorFresh different cleanFuture owned).val rfl roomData fresh2 different v1 v11 v12 sourceLive sourceCached lenLive lenUncached exprLive exprUncached body
    identity callee location frameRace race ghost shallow cached present metadata notConstructed backend thread active threadCache unchecked noGc fixed source
    rangePositive exprUnheld size count countPositive within all live0 cache0 live7 cache7 live8 cache8 live9 cache9 live10 cache10 live13 cache13
    dead15 cache15 dead16 cache16

theorem executes
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat)
    (dispatchFuel : limits.callDispatch = budget+1) (span : PreparedContracts.FixedSpanQuery)
    (precise : options.retag.preciseInteriorMut = false) (implicitWrites : options.retag.implicitWrites = false)
    (debug : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (dynamicEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (positive : (0 : UInt64) < len) (nonnull : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (target : UniIndex)
    (first : GeneralBorrowFreshSharedSequence.Data entry.allocation.extra tracker.global.nextPointerTag target offset len)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (GeneralBorrowRange.LocationOwned entry.allocation.extra tracker.global.protectedTags target .Write)
      offset (offset+len) entry.allocation.extra.locations)
    (noFree : entry.allocation.extra.tagMapping.deassigned.back? = none)
    (room : entry.allocation.extra.tagMapping.mapping.size+1 ≤ 4294967295)
    (fresh2 : (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag.value < 18446744073709551615)
    (tagFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping
      (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag)
    (protectorFresh : GeneralBorrowProtector.Fresh entry.allocation.extra
      (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag)
    (different : tracker.global.nextPointerTag ≠ (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag)
    (cleanFuture : GeneralRangeMapState.Every (fun location : LocationTree =>
      location.perms.get (GeneralBorrowFreshSharedNext.future entry.allocation.extra) = none) entry.allocation.extra.locations)
    (v1 : 1 < frame.locals.size) (v11 : 11 < frame.locals.size) (v12 : 12 < frame.locals.size)
    (sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id first.parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference)
    (lenLive : frame.locals[11].value = .live (.immediate .uninit)) (lenUncached : frame.locals[11].layout = none)
    (exprLive : frame.locals[12].value = .live (.immediate .uninit)) (exprUncached : frame.locals[12].layout = none)
    (body : frame.body = RootBody.reflected.body.body) (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) (location : frame.location = .mir ⟨2,11⟩)
    (frameRace : frame.extra.dataRace = none) (race : machine.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (backend : machine.user.payload.payload.user.backend = .none)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (threadCache : thread.topUserRelevantFrame = some 0)
    (unchecked : ((config options (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((config options (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) (source : PreparedContracts.SourceComparator)
    (rangePositive : offset.toNat < (offset+len).toNat)
    (exprUnheld : tracker.global.protectedTags.contains tracker.global.nextPointerTag = false)
    (size : frame.locals.size=25)
    (count : UInt64) (countPositive : (0 : UInt64)<count) (within : count≤len/2)
    (all : CopyHelperCleanup.AllImmediate frame)
    (live0 : (frame.locals[0]'(by omega)).value=.live (.immediate .uninit)) (cache0 : (frame.locals[0]'(by omega)).layout=none)
    (live7 : (frame.locals[7]'(by omega)).value=.live (.immediate .uninit)) (cache7 : (frame.locals[7]'(by omega)).layout=none)
    (live8 : (frame.locals[8]'(by omega)).value=.live (.immediate .uninit)) (cache8 : (frame.locals[8]'(by omega)).layout=none)
    (live9 : (frame.locals[9]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cache9 : (frame.locals[9]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (live10 : (frame.locals[10]'(by omega)).value=.live (.immediate .uninit)) (cache10 : (frame.locals[10]'(by omega)).layout=none)
    (live13 : (frame.locals[13]'(by omega)).value=.live (.immediate .uninit)) (cache13 : (frame.locals[13]'(by omega)).layout=none)
    (dead15 : (frame.locals[15]'(by omega)).value=.dead) (cache15 : (frame.locals[15]'(by omega)).layout=none)
    (dead16 : (frame.locals[16]'(by omega)).value=.dead) (cache16 : (frame.locals[16]'(by omega)).layout=none)
 :
    ∃ (result : CompilerFrameContext.ActualFrame) (done : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (released : BorrowTree) (ended : MachineHooks.BorrowState),
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] frame machine) (Storage.withCurrent #[] result done) ∧
      result.location = .mir ⟨6,7⟩ ∧ done.borrowTracker=some ended ∧
      done.memory.live.find? (fun row => row.1 == id) = some (id,GeneralBorrowFreshSharedPop.withTree entry released) ∧
      result.body=frame.body ∧ result.bodyIdentity=frame.bodyIdentity ∧ result.functionInstance=frame.functionInstance ∧
      result.extra=frame.extra ∧ result.locals.size=25 ∧ result.locals[1]?=frame.locals[1]? ∧ result.locals[2]?=frame.locals[2]? ∧
      result.locals[15]?=some ⟨.live (.immediate .uninit),none⟩ ∧ result.locals[16]?=some ⟨.live (.immediate .uninit),none⟩ ∧
      CopyHelperCleanup.AllImmediate result ∧
      GeneralRangeMapOrigins.OwnedOn (GeneralBorrowRange.LocationOwned released ended.global.protectedTags target .Write)
        offset (offset+len) released.locations := by
  obtain ⟨result,done,released,ended,previous,_,_,_,_,_⟩ := executes_full options limits remaining budget dispatchFuel span precise implicitWrites debug cmp dynamicFuel validityFuel dynamicEq validationEq
    id entry base offset len positive nonnull signedFits frame machine tracker enabled defaultMode fresh target first capacity owned noFree room
    fresh2 tagFresh protectorFresh different cleanFuture v1 v11 v12 sourceLive sourceCached lenLive lenUncached exprLive exprUncached body
    identity callee location frameRace race ghost shallow cached present metadata notConstructed backend thread active threadCache unchecked noGc fixed source
    rangePositive exprUnheld size count countPositive within all live0 cache0 live7 cache7 live8 cache8 live9 cache9 live10 cache10 live13 cache13
    dead15 cache15 dead16 cache16
  exact ⟨result,done,released,ended,previous⟩

end
end DuplicatePrefix.GenericSharedLenAccepted
