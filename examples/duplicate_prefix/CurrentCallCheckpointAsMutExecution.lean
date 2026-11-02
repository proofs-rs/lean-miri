import duplicate_prefix.CurrentCallResourceAsMutCall
import duplicate_prefix.CurrentCallResourceLenRoots
import duplicate_prefix.GenericLenAcceptedPrelude
import duplicate_prefix.CurrentCallMutableReference
import duplicate_prefix.CurrentCallAsMutArgumentCopy
import duplicate_prefix.CurrentCallResourceFnEntry

namespace DuplicatePrefix.CurrentCallCheckpointAsMutExecution
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization CurrentCallResourceEntryBody
open CanonicalConfigFacts ActualReferenceContext
open GeneralBorrowRawDefaultExpression RootReferenceInfo RootReferenceTrees GeneralRangeMapOrigins
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

theorem execute
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (parentTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808) (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (literalReadCompleted : (entry.allocation.extra.performBorrowAccessRange (.concrete parentTag)
      (Size.ofBytes offset) (Size.ofBytes len) .Read
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (childDone : ((entry.allocation.extra.performBorrowAccessRange (.concrete parentTag)
      (Size.ofBytes offset) (Size.ofBytes len) .Read
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).tree.newChild
      (Size.ofBytes offset) (.concrete parentTag) tracker.global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).outcome = .ok ())
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (destValid : (15 : MIR.LocalId) < caller.locals.size) (old : Immediate Provenance)
    (destLive : caller.locals[15].value = .live (.immediate old))
    (uncached : caller.locals[15].layout = none)
    (callerClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] caller machine)).metadata = PreparedReflection.actual.runtime)
    (cacheOrigins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] caller machine)))
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent #[] (AsMutUncachedCall.cachedCaller caller destValid) (AsMutPtrReturn.accountedMachine options remaining span machine))
      (LocalPlaces.localRuntimePlace 0 (AsMutUncachedCall.cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (topPresent : (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent #[] (AsMutUncachedCall.cachedCaller caller destValid) (AsMutPtrReturn.accountedMachine options remaining span machine))
      (LocalPlaces.localRuntimePlace 0 (AsMutUncachedCall.cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack.frames[index]? = some current)
    (source : PreparedContracts.SourceComparator)
    (sourceBody : caller.body = RootBody.reflected.body.body)
    (sourceIdentity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (sourceCallee : caller.functionInstance = RootBody.reflected.functionInstance)
    (sourceLocation : caller.location = .mir ⟨6,8⟩)
    (valid16 : (16 : MIR.LocalId) < caller.locals.size)
    (value16 : caller.locals[16].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (cached16 : caller.locals[16].layout = some ActualReferenceMetadata.reference)
    (backend : machine.user.payload.payload.user.backend = .none)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic=false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval=0)
    (fixed : machine.threads.fixedScheduling=true) :

    let cfg := config options remaining span
    let before := Storage.withCurrent #[] (AsMutUncachedCall.cachedCaller caller destValid) (AsMutPtrReturn.accountedMachine options remaining span machine)
    let destination := (LocalPlaces.localRuntimePlace 0 (AsMutUncachedCall.cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let adjusted := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let postMachine := (AsMutPush.completed options.userRelevantCrates before destination current).machine
    let finalTree := CurrentCallAsMutArgumentCopy.Argument.finalTree entry.allocation.extra tracker parentTag offset len
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine postMachine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory postMachine.memory id entry finalTree}
    let frame := CurrentCallAsMutArgumentCopy.Entry.initialized options before destination value adjusted id tracker.global.nextPointerTag
    ∃ done : CompilerFrameContext.ActualFrame,
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent #[] caller machine) =
      ((Storage.withCurrent (#[(AsMutUncachedCall.cachedCaller caller destValid)])
        (CurrentCallAsMutArgumentCopy.Entry.initialized options before destination value adjusted id tracker.global.nextPointerTag) resultMachine),.ok true) ∧
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent (#[(AsMutUncachedCall.cachedCaller caller destValid)]) frame resultMachine)
        (Storage.withCurrent (#[(AsMutUncachedCall.cachedCaller caller destValid)]) done resultMachine) ∧
      done.location = .mir ⟨0,10⟩ ∧
      done.locals[0]? = some ⟨.live (.immediate (.scalar (Scalar.fromPointer
        (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset)))))),some CopyCompilerFacts.destPointerLayout⟩ ∧
      done.body = frame.body ∧ done.bodyIdentity = frame.bodyIdentity ∧
      done.functionInstance = frame.functionInstance ∧
      done.extra = frame.extra ∧ done.returnPlace = frame.returnPlace ∧ done.returnContinuation = frame.returnContinuation ∧
      done.vaList = frame.vaList ∧ done.localsIdentity = frame.localsIdentity ∧
      done.locals[1]? = frame.locals[1]? ∧ done.locals.size = 5 ∧
      (done.locals[2]?.map (·.value)) = some .dead ∧
      (done.locals[3]?.map (·.value)) = some .dead ∧
      (done.locals[4]?.map (·.value)) = some .dead ∧
      GeneralBorrowForestMixedLenCallReturnRuntime.RuntimeFacts options remaining span resultMachine resultMachine ∧
      GeneralBorrowForestMixedLenBeforeReturn.RootCache #[] resultMachine ∧
      done.extra.borrowTracker = some (GeneralBorrowFnEntryRegistration.registered tracker.global {} id fresh).2 ∧ done.extra.dataRace = none ∧
      done.body = HelperCompilerFacts.asMutPtrBody.body ∧
      done.returnPlace.toRuntimePlace = LocalPlaces.localRuntimePlace 0 (AsMutUncachedCall.cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout ∧
      done.returnContinuation = .goto (some 7) .Continue ∧ done.vaList = #[] ∧
      done.locals[1]? = some ⟨.live (.immediate adjusted),some ActualReferenceMetadata.reference⟩ := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let initial := Storage.withCurrent #[] caller machine
  let next := AsMutPtrReturn.accountedMachine options remaining span machine
  let nextState := Storage.withCurrent #[] caller next
  have nextGhost : next.user.payload.ghost = false := (AsMutPtrReturn.accounted_ghost options remaining span machine).trans ghost
  have nextShallow : next.user.payload.validation = .Shallow := (AsMutPtrReturn.accounted_validation options remaining span machine).trans shallow
  have nextBackend : next.user.payload.payload.user.backend = .none := by
    unfold next AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact backend
  have nextAddress : next.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ := by
    unfold next AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact cachedAddress
  have nextMetadata : (EvalProjectionMachine.arrays.get nextState).metadata = PreparedReflection.actual.runtime := by
    unfold nextState next AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact metadata
  have nextOrigins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get nextState) := by
    unfold nextState next AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact cacheOrigins
  obtain ⟨done,called,trace,location,pointerDone,body,identity,callee,extra,returnPlace,continuation,varargs,localsId,sourceSlot,sizeDone,dead2,dead3,dead4⟩ :=
    CurrentCallAsMutArgumentCopy.Body.caller_before_return options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
      id entry base offset len parentTag positive nonzero signedFits bounds caller next tracker enabled defaultMode fresh
      literalReadCompleted childDone capacity destValid old destLive uncached callerClocks nextGhost nextShallow nextAddress present race nextMetadata nextOrigins
      thread index current active top topPresent source sourceBody sourceIdentity sourceCallee sourceLocation valid16 value16 cached16 nextBackend
  let root := AsMutUncachedCall.cachedCaller caller destValid
  let beforePush := Storage.withCurrent #[] root next
  let destination := (LocalPlaces.localRuntimePlace 0 root 15 CopyCompilerFacts.destPointerLayout).stackView
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let post := (AsMutPush.completed options.userRelevantCrates beforePush destination current).machine
  let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine post tracker fresh)
    (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
    memory := RetagEntry.updatedMemory post.memory id entry (CurrentCallAsMutArgumentCopy.Argument.finalTree entry.allocation.extra tracker parentTag offset len)}
  let frame := CurrentCallAsMutArgumentCopy.Entry.initialized options beforePush destination value adjusted id tracker.global.nextPointerTag
  have frameExtra : done.extra = frame.extra := extra
  obtain ⟨_,_,postRace,postAddress,postGhost,postShallow,postUser,postFixed⟩ :=
    AsMutPushPreserves.preserves options.userRelevantCrates beforePush destination current
  change post.user.payload.payload.user = next.user.payload.payload.user at postUser
  have helperGhost : resultMachine.user.payload.ghost = false := by
    change post.user.payload.ghost = false
    exact postGhost.trans nextGhost
  have helperShallow : resultMachine.user.payload.validation = .Shallow := by
    change post.user.payload.validation = .Shallow
    exact postShallow.trans nextShallow
  have helperRace : resultMachine.dataRace = none := by
    change post.dataRace = none
    exact postRace.trans race
  have helperBackend : resultMachine.user.payload.payload.user.backend = .none := by
    change post.user.payload.payload.user.backend = .none
    rw [postUser]
    exact nextBackend
  have nextFlags := RootZeroCompleteState.tick_flags options remaining span machine
  have nextUnchecked : (cfg.terminators.getControl next.user).checkedArithmetic = false := nextFlags.1.trans unchecked
  have nextNoGc : (cfg.terminators.getControl next.user).gcInterval = 0 := nextFlags.2.trans noGc
  have helperUnchecked : (cfg.terminators.getControl resultMachine.user).checkedArithmetic = false := by
    change (cfg.terminators.getControl post.user).checkedArithmetic = false
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators] at nextUnchecked ⊢
    simp only [EvalTerminatorMachine.genericHooks] at nextUnchecked ⊢
    rw [postUser]
    exact nextUnchecked
  have helperNoGc : (cfg.terminators.getControl resultMachine.user).gcInterval = 0 := by
    change (cfg.terminators.getControl post.user).gcInterval = 0
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators] at nextNoGc ⊢
    simp only [EvalTerminatorMachine.genericHooks] at nextNoGc ⊢
    rw [postUser]
    exact nextNoGc
  have helperFixed : resultMachine.threads.fixedScheduling = true := by
    change post.threads.fixedScheduling = true
    exact postFixed.trans fixed
  let supply := AsMutPush.fresh next
  let rank := (AsMutFrame.rawFrame options.userRelevantCrates supply.1 destination supply.2).extra.userRelevance
  let nextThread := if rank >= current.extra.userRelevance then {thread with topUserRelevantFrame := some 1} else thread
  have helperActive : resultMachine.threads.activeThread? = some nextThread := by
    change (GenericPushRelevance.afterPush supply.1 1 rank current.extra.userRelevance).threads.activeThread? = some nextThread
    exact AsMutPushPreserves.active_after_push supply.1 thread active 1 rank current.extra.userRelevance
  have indexBound : index < 2 := by
    have known := (Array.getElem?_eq_some_iff.mp topPresent).1
    simpa only [AsMutPush.pushed,Storage.withCurrent,Array.size_push,Array.size_empty] using known
  have oldBound (i : Nat) (same : thread.topUserRelevantFrame = some i) : i < 2 := by
    have equal : i = index := by simpa only [FrameRelevance.top,same,Option.orElse_some,Option.some.injEq] using top
    simpa only [equal] using indexBound
  have cacheBound (i : Nat) (same : nextThread.topUserRelevantFrame = some i) : i < 2 := by
    unfold nextThread at same
    split at same
    · have equal : (1 : Nat) = i := by simpa only [Option.some.injEq] using same
      omega
    · exact oldBound i same
  have helperRuntime : GeneralBorrowForestMixedLenCallReturnRuntime.RuntimeFacts options remaining span resultMachine resultMachine :=
    ⟨helperGhost,helperShallow,helperRace,rfl,rfl,rfl,helperBackend,helperUnchecked,helperNoGc,helperFixed,⟨nextThread,helperActive⟩⟩
  have helperCache : GeneralBorrowForestMixedLenBeforeReturn.RootCache #[] resultMachine :=
    ⟨fun _ => ⟨nextThread,helperActive,cacheBound⟩⟩
  have helperBorrow : done.extra.borrowTracker = some (GeneralBorrowFnEntryRegistration.registered tracker.global {} id fresh).2 := by
    rw [frameExtra]
    rfl
  have frameRace : frame.extra.dataRace = none := by
    change machine.dataRace.map _ = none
    rw [race]
    rfl
  have helperClocks : done.extra.dataRace = none := by rw [frameExtra];exact frameRace
  have helperBody : done.body = HelperCompilerFacts.asMutPtrBody.body := body
  have helperDestination : done.returnPlace.toRuntimePlace = LocalPlaces.localRuntimePlace 0 root 15 CopyCompilerFacts.destPointerLayout := by
    rw [returnPlace]
    rfl
  have helperContinuation : done.returnContinuation = .goto (some 7) .Continue := by rw [continuation];rfl
  have helperVarargs : done.vaList = #[] := by rw [varargs];rfl
  have slots := GeneralBorrowRawAsMutShape.locals options beforePush destination value adjusted id tracker.global.nextPointerTag
  have helperOne : done.locals[1]? = some ⟨.live (.immediate adjusted),some ActualReferenceMetadata.reference⟩ := by
    rw [sourceSlot]
    change frame.locals[1]? = _
    rw [show frame.locals = _ from slots]
    rfl
  have accounting := SourceControl.before_terminator cfg limits () initial
    (CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span)
    (CanonicalConfigFacts.actual_term_set_set options () (remaining+1) span) unchecked noGc fixed
  have accounting' : (ExecutionMachine.stepHooks cfg limits).beforeTerminator () initial = (nextState,.ok ()) := accounting
  let block := RootBody.reflected.body.body.basicBlocks[6]'(by with_unfolding_all decide +kernel)
  have blockAt : caller.body.basicBlocks[6]? = some block := by rw [sourceBody];simp [block]
  have noStatement : block.statements[8]? = none := by with_unfolding_all rfl
  refine ⟨done,?_,
    trace,location,pointerDone,body,identity,callee,extra,returnPlace,continuation,varargs,localsId,sourceSlot,sizeDone,dead2,dead3,dead4,helperRuntime,helperCache,helperBorrow,helperClocks,helperBody,helperDestination,helperContinuation,helperVarargs,helperOne⟩
  apply GenericCallStages.source_step cfg limits () initial nextState _ caller ⟨6,8⟩ block
    HelperCompilerFacts.asMutPtrCall.function #[AsMutEvaluateCall.argument] ⟨15,#[]⟩ (some 7) .Continue
    AsMutCallTerminator.sourceKind AsMutCallTerminator.fnSpan
    (by simp [initial,Storage.withCurrent,Stack.currentFrame?]) sourceLocation blockAt noStatement AsMutCallTerminator.source_call accounting' called
  simp [Storage.withCurrent,nextState]




structure Helper (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : Before) (tracker : MachineHooks.BorrowState) (id : AllocId) (offset len : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (caller : CompilerFrameContext.ActualFrame)
    (base : UInt64) (parentTag : BorTag) (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (valid15 : (15 : MIR.LocalId)<caller.locals.size) where
  output : GeneralBorrowForestFnEntry.Output
  literal : output=CurrentCallTypedFnEntry.literal entry.allocation.extra tracker.global {} id fresh (.concrete id parentTag) offset len
  helper : CompilerFrameContext.ActualFrame
  machine : Before
  trace : SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
    (Storage.withCurrent #[] caller before)
    (Storage.withCurrent #[(AsMutUncachedCall.cachedCaller caller valid15)] helper machine)
  memory : machine.memory=RetagEntry.updatedMemory before.memory id entry output.child.tree
  addresses : machine.user.addresses=before.user.addresses
  types : machine.user.payload.payload.user.types=before.user.payload.payload.user.types
  extras : machine.user.payload.payload.user.runtime.extras=before.user.payload.payload.user.runtime.extras
  live : machine.memory.live.find? (fun row=>row.1==id)=some (id,{entry with allocation:=entry.allocation.setExtra output.child.tree})
  tracked : machine.borrowTracker=some {tracker with global:=output.global}
  runtime : GeneralBorrowForestMixedLenCallReturnRuntime.RuntimeFacts options remaining span machine machine
  cache : GeneralBorrowForestMixedLenBeforeReturn.RootCache #[] machine
  borrow : helper.extra.borrowTracker=some output.frame
  frameOwned : output.frame.protectedTags=#[(id,output.tag)]
  clocks : helper.extra.dataRace=none
  body : helper.body=HelperCompilerFacts.asMutPtrBody.body
  location : helper.location=.mir ⟨0,10⟩
  size : helper.locals.size=5
  returned : helper.locals[0]?=some ⟨.live (.immediate (.scalar (Scalar.fromPointer
    (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
    (Pointer.new (.concrete id output.tag) (Size.ofBytes (base+offset)))))),some CopyCompilerFacts.destPointerLayout⟩
  argument : Immediate Provenance
  argumentAt : helper.locals[1]?.map (·.value)=some (.live (.immediate argument))
  dead2 : helper.locals[2]?.map (·.value)=some .dead
  dead3 : helper.locals[3]?.map (·.value)=some .dead
  dead4 : helper.locals[4]?.map (·.value)=some .dead
  destination : helper.returnPlace.toRuntimePlace=LocalPlaces.localRuntimePlace 0 (AsMutUncachedCall.cachedCaller caller valid15) 15 CopyCompilerFacts.destPointerLayout
  continuation : helper.returnContinuation=.goto (some 7) .Continue
  varargs : helper.vaList=#[]
  callerValid : (15 : MIR.LocalId)<(AsMutUncachedCall.cachedCaller caller valid15).locals.size
  callerLive : (AsMutUncachedCall.cachedCaller caller valid15).locals[15].value=.live (.immediate .uninit)
  callerCached : (AsMutUncachedCall.cachedCaller caller valid15).locals[15].layout=some CopyCompilerFacts.destPointerLayout
  callerClocks : (AsMutUncachedCall.cachedCaller caller valid15).extra.dataRace=none

theorem helper
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (parentTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808) (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (literalReadCompleted : (entry.allocation.extra.performBorrowAccessRange (.concrete parentTag)
      (Size.ofBytes offset) (Size.ofBytes len) .Read
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (childDone : ((entry.allocation.extra.performBorrowAccessRange (.concrete parentTag)
      (Size.ofBytes offset) (Size.ofBytes len) .Read
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).tree.newChild
      (Size.ofBytes offset) (.concrete parentTag) tracker.global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).outcome = .ok ())
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (destValid : (15 : MIR.LocalId) < caller.locals.size)
    (destLive : caller.locals[15].value = .live (.immediate .uninit))
    (uncached : caller.locals[15].layout = none)
    (callerClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] caller machine)).metadata = PreparedReflection.actual.runtime)
    (cacheOrigins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] caller machine)))
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent #[] (AsMutUncachedCall.cachedCaller caller destValid) (AsMutPtrReturn.accountedMachine options remaining span machine))
      (LocalPlaces.localRuntimePlace 0 (AsMutUncachedCall.cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (topPresent : (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent #[] (AsMutUncachedCall.cachedCaller caller destValid) (AsMutPtrReturn.accountedMachine options remaining span machine))
      (LocalPlaces.localRuntimePlace 0 (AsMutUncachedCall.cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack.frames[index]? = some current)
    (source : PreparedContracts.SourceComparator)
    (sourceBody : caller.body = RootBody.reflected.body.body)
    (sourceIdentity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (sourceCallee : caller.functionInstance = RootBody.reflected.functionInstance)
    (sourceLocation : caller.location = .mir ⟨6,8⟩)
    (valid16 : (16 : MIR.LocalId) < caller.locals.size)
    (value16 : caller.locals[16].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (cached16 : caller.locals[16].layout = some ActualReferenceMetadata.reference)
    (backend : machine.user.payload.payload.user.backend = .none)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic=false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval=0)
    (fixed : machine.threads.fixedScheduling=true) : Nonempty (Helper options limits remaining span machine tracker id offset len entry caller base parentTag fresh destValid) := by
  obtain ⟨done,step,trace,location,pointerDone,body,identity,callee,extra,returnPlace,continuation,varargs,localsId,sourceSlot,sizeDone,
    dead2,dead3,dead4,helperRuntime,helperCache,helperBorrow,helperClocks,helperBody,helperDestination,helperContinuation,helperVarargs,helperOne⟩ :=
    execute options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
      id entry base offset len parentTag positive nonzero signedFits bounds caller machine tracker enabled defaultMode fresh
      literalReadCompleted childDone capacity destValid .uninit destLive uncached callerClocks ghost shallow cachedAddress present race metadata cacheOrigins
      thread index current active top topPresent source sourceBody sourceIdentity sourceCallee sourceLocation valid16 value16 cached16 backend unchecked noGc fixed
  let output:=CurrentCallTypedFnEntry.literal entry.allocation.extra tracker.global {} id fresh (.concrete id parentTag) offset len
  have tag : output.tag=tracker.global.nextPointerTag:=rfl
  have global : output.global=(GeneralBorrowFnEntryRegistration.registered tracker.global {} id fresh).1:=rfl
  have frameEq : output.frame=(GeneralBorrowFnEntryRegistration.registered tracker.global {} id fresh).2:=rfl
  have treeEq : output.child.tree=CurrentCallAsMutArgumentCopy.Argument.finalTree entry.allocation.extra tracker parentTag offset len:=rfl
  let root:=AsMutUncachedCall.cachedCaller caller destValid
  let next:=AsMutPtrReturn.accountedMachine options remaining span machine
  let beforePush:=Storage.withCurrent #[] root next
  let destination:=(LocalPlaces.localRuntimePlace 0 root 15 CopyCompilerFacts.destPointerLayout).stackView
  let post:=(AsMutPush.completed options.userRelevantCrates beforePush destination current).machine
  let finalTree:=CurrentCallAsMutArgumentCopy.Argument.finalTree entry.allocation.extra tracker parentTag offset len
  let resultMachine:={TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine post tracker fresh)
    (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
    memory:=RetagEntry.updatedMemory post.memory id entry finalTree}
  let argument:=(RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  obtain ⟨postMemory,_,_,postAddresses,_,_,postUser,_⟩:=AsMutPushPreserves.preserves options.userRelevantCrates beforePush destination current
  have memoryEq : resultMachine.memory=RetagEntry.updatedMemory machine.memory id entry output.child.tree:=by
    change RetagEntry.updatedMemory post.memory id entry finalTree=_
    rw [postMemory]
    change RetagEntry.updatedMemory machine.memory id entry finalTree=_
    dsimp only [finalTree]
    rw [←treeEq]
  have trackedEq : resultMachine.borrowTracker=some {tracker with global:=output.global}:=by
    change some (TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag)=_
    rw [global]
    rfl
  have currentLive : resultMachine.memory.live.find? (fun row=>row.1==id)=some (id,{entry with allocation:=entry.allocation.setExtra output.child.tree}):=by
    rw [memoryEq]
    exact StackPopRelease.lookup_commit_same _ _ _ _
  have currentAddress : resultMachine.user.addresses=machine.user.addresses:=by
    change post.user.addresses=machine.user.addresses
    rw [postAddresses]
    change next.user.addresses=machine.user.addresses
    unfold next AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have currentTypes : resultMachine.user.payload.payload.user.types=machine.user.payload.payload.user.types:=by
    change post.user.payload.payload.user.types=machine.user.payload.payload.user.types
    change post.user.payload.payload.user=next.user.payload.payload.user at postUser
    rw [postUser]
    unfold next AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have currentExtras : resultMachine.user.payload.payload.user.runtime.extras=machine.user.payload.payload.user.runtime.extras:=by
    change post.user.payload.payload.user.runtime.extras=machine.user.payload.payload.user.runtime.extras
    change post.user.payload.payload.user=next.user.payload.payload.user at postUser
    rw [postUser]
    unfold next AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have frameOwned : output.frame.protectedTags=#[(id,output.tag)]:=by
    rw [frameEq,tag]
    simp only [GeneralBorrowFnEntryRegistration.registered,GlobalState.addProtector,FrameState.addProtector,Array.push_empty]
  have rootValid : (15 : MIR.LocalId)<root.locals.size:=by simpa only [root,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,Array.size_set] using destValid
  have rootLive : root.locals[15].value=.live (.immediate .uninit):=by simpa only [root,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set_self] using destLive
  have rootCached : root.locals[15].layout=some CopyCompilerFacts.destPointerLayout:=by simp [root,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout]
  have argumentAt : done.locals[1]?.map (·.value)=some (.live (.immediate argument)):=by
    simpa only [Option.map_some] using congrArg (Option.map LocalState.value) helperOne
  have returned : done.locals[0]?=some ⟨.live (.immediate (.scalar (Scalar.fromPointer
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id output.tag) (Size.ofBytes (base+offset)))))),some CopyCompilerFacts.destPointerLayout⟩:=by
    rw [tag]
    exact pointerDone
  refine ⟨{
    output:=output
    literal:=rfl
    helper:=done
    machine:=resultMachine
    trace:=.next step trace
    memory:=memoryEq
    live:=currentLive
    addresses:=currentAddress
    types:=currentTypes
    extras:=currentExtras
    tracked:=trackedEq
    runtime:=helperRuntime
    cache:=helperCache
    borrow:=helperBorrow
    frameOwned:=frameOwned
    clocks:=helperClocks
    body:=helperBody
    location:=location
    size:=sizeDone
    returned:=returned
    argument:=argument
    argumentAt:=argumentAt
    dead2:=dead2
    dead3:=dead3
    dead4:=dead4
    destination:=helperDestination
    continuation:=helperContinuation
    varargs:=helperVarargs
    callerValid:=rootValid
    callerLive:=rootLive
    callerCached:=rootCached
    callerClocks:=callerClocks }⟩
end
end DuplicatePrefix.CurrentCallCheckpointAsMutExecution
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointAsMutExecution" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved common AsMut execution dependency {dependency}"
