import duplicate_prefix.LanguageGuardBody
import duplicate_prefix.CopyRootGuardState
import duplicate_prefix.CopyHelperCleanup

/-! Actual copy-call language/runtime guard prefix with independent
statement-execution and typed-validation budgets. -/
namespace DuplicatePrefix.CurrentCallCopyGuard.Language
open Miri Miri.Input Miri.ABI Miri.MIR Miri.Interpreter Miri.Memory Miri.TreeBorrows
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem from_entry
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining budget fuel statementFuel : Nat) (dispatchFuel : limits.callDispatch = budget+1)
    (validationFuel : options.limits.validation = fuel+1)
    (statementFuelEq : limits.validation = statementFuel+1)
    (span : PreparedContracts.FixedSpanQuery) (source : PreparedContracts.SourceComparator)
    (cmp : ProjectionMetadataFacts.NullComparator) (debugOff : options.place.debugAssertions = false)
    (frames : Array CompilerFrameContext.ActualFrame) (copy frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = CopyPreconditions.Bodies.checkLanguage.loaded.body)
    (identity : frame.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity)
    (callee : frame.functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance)
    (location : frame.location = .mir ⟨0,0⟩) (size : frame.locals.size = 3)
    (valid0 : (0 : MIR.LocalId) < frame.locals.size)
    (live0 : frame.locals[0].value = .live (.immediate .uninit))
    (uncached0 : frame.locals[0].layout = none)
    (valid1 : (1 : MIR.LocalId) < frame.locals.size)
    (dead1 : frame.locals[1].value = .dead)
    (uncached1 : frame.locals[1].layout = none)
    (valid2 : (2 : MIR.LocalId) < frame.locals.size)
    (dead2 : frame.locals[2].value = .dead)
    (uncached2 : frame.locals[2].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (noRace : machine.dataRace = none) (backend : machine.user.payload.payload.user.backend = .none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .Default)
    (thread : Concurrency.ThreadRecord) (threadIndex : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (RuntimeZeroEntryFacts.pushed options.userRelevantCrates
      (Storage.withCurrent (frames.push copy) (RuntimeZeroUncached.cachedCaller (ParentUnitPrelude.afterPrelude frame valid1 valid2)
        (by simpa [ParentUnitPrelude.afterPrelude,SourceSteps.liveFrame,LocalPlaces.cachePlaceLayout] using valid1))
        (RuntimeZeroStep.accountedMachine options remaining span machine))
      (RuntimeZeroEntry.destination (frames.push copy) (ParentUnitPrelude.afterPrelude frame valid1 valid2))).stack
      thread.topUserRelevantFrame = some threadIndex)
    (present : (RuntimeZeroEntryFacts.pushed options.userRelevantCrates
      (Storage.withCurrent (frames.push copy) (RuntimeZeroUncached.cachedCaller (ParentUnitPrelude.afterPrelude frame valid1 valid2)
        (by simpa [ParentUnitPrelude.afterPrelude,SourceSteps.liveFrame,LocalPlaces.cachePlaceLayout] using valid1))
        (RuntimeZeroStep.accountedMachine options remaining span machine))
      (RuntimeZeroEntry.destination (frames.push copy) (ParentUnitPrelude.afterPrelude frame valid1 valid2))).stack.frames[threadIndex]? = some current)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (copyValid5 : (5 : MIR.LocalId) < copy.locals.size)
    (copyLive5 : copy.locals[5].value = .live (.immediate .uninit))
    (copyCached5 : copy.locals[5].layout = some RootCompilerFacts.boolLayout)
    (copyNoClocks : copy.extra.dataRace = none)
    (destination : frame.returnPlace.toRuntimePlace =
      LocalPlaces.localRuntimePlace frames.size copy 5 RootCompilerFacts.boolLayout)
    (target : BasicBlockId) (unwind : UnwindAction)
    (continuation : frame.returnContinuation = .goto (some target) unwind)
    (varargs : frame.vaList = #[])
    (borrowFrame : FrameState) (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (empty : borrowFrame.protectedTags = #[]) :
    ∃ finalMachine,
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent (frames.push copy) frame machine)
        (Storage.withCurrent frames (ParentFalseReturn.returnedCallerFrame copy copyValid5 target) finalMachine) ∧
      LanguageGuardReturn.Preserves options remaining span machine finalMachine ∧
      (∃ finalThread, finalMachine.threads.activeThread? = some finalThread) ∧
      CallSafety.NoUBBeforeReturn (LanguageGuardBody.safetyContext options limits remaining span) (frames.size+2)
        (Storage.withCurrent (frames.push copy) frame machine) := by
  let ready := ParentUnitPrelude.afterPrelude frame valid1 valid2
  have readySize : ready.locals.size = 3 := by
    simp [ready,ParentUnitPrelude.afterPrelude,SourceSteps.liveFrame,LocalPlaces.cachePlaceLayout,size]
  have readyValid0 : (0 : MIR.LocalId) < ready.locals.size := by rw [readySize];decide
  have readyValid1 : (1 : MIR.LocalId) < ready.locals.size := by rw [readySize];decide
  have readyValid2 : (2 : MIR.LocalId) < ready.locals.size := by rw [readySize];decide
  have first := ParentUnitPrelude.actual_parent_three_statement_steps_exact options limits remaining span
    debugOff statementFuel statementFuelEq (frames.push copy) frame machine valid1 valid2 body identity callee location
    dead1 dead2 uncached2 noClocks ghost shallow
  obtain ⟨afterFrame,stepFirst,stepSecond,stepThird,readyEq⟩ := first
  have tail := LanguageGuardReturn.from_call options limits remaining budget fuel dispatchFuel validationFuel
    span source cmp debugOff frames copy ready machine body identity callee rfl readySize readyValid0
    (by simpa [ready,ParentUnitPrelude.afterPrelude,SourceSteps.liveFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set] using live0)
    (by simpa [ready,ParentUnitPrelude.afterPrelude,SourceSteps.liveFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set] using uncached0)
    readyValid1
    (by simp [ready,ParentUnitPrelude.afterPrelude,SourceSteps.liveFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set,valid1])
    (by simpa [ready,ParentUnitPrelude.afterPrelude,SourceSteps.liveFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set] using uncached1)
    readyValid2
    (by simp [ready,ParentUnitPrelude.afterPrelude,SourceSteps.liveFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set,valid2])
    (some CopyHelperUnit.layout)
    (by simp [ready,ParentUnitPrelude.afterPrelude,SourceSteps.liveFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set,valid2])
    noClocks noRace backend ghost shallow tracker tracked mode thread threadIndex current active top present
    unchecked noGc fixed copyValid5 copyLive5 copyCached5 copyNoClocks destination target unwind continuation
    varargs borrowFrame frameTracked empty
  obtain ⟨finalMachine,trace,preserves,finalActive⟩ := tail
  have stepThird' := stepThird
  simp only [Nat.reduceAdd,readyEq] at stepThird'
  have fullTrace : SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
      (Storage.withCurrent (frames.push copy) frame machine)
      (Storage.withCurrent frames (ParentFalseReturn.returnedCallerFrame copy copyValid5 target) finalMachine) :=
    .next stepFirst (.next stepSecond (.next stepThird' trace))
  have safe := SuccessfulTrace.no_ub (LanguageGuardBody.safetyContext options limits remaining span) (frames.size+2)
    (Storage.withCurrent (frames.push copy) frame machine)
    (Storage.withCurrent frames (ParentFalseReturn.returnedCallerFrame copy copyValid5 target) finalMachine)
    (by simp [CallSafety.IsCallEntry,CallSafety.frameDepth,Storage.withCurrent])
    fullTrace
    (by simp [CallSafety.pastCallBoundary,CallSafety.frameDepth,Storage.withCurrent])
  exact ⟨finalMachine,fullTrace,preserves,finalActive,safe⟩

end DuplicatePrefix.CurrentCallCopyGuard.Language

namespace DuplicatePrefix.CurrentCallCopyGuard
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

variable (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
  (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
  (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
  (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
  (sourcePointer destinationPointer : Scalar Provenance) (n : UInt64)
  (input : CopyRootEntry.Input options limits remaining span frames caller machine sourcePointer destinationPointer n)

private theorem prepared_fifth (original : CompilerFrameContext.ActualFrame)
    (valid4 : (4 : MIR.LocalId) < original.locals.size)
    (valid5 : (5 : MIR.LocalId) < original.locals.size) :
    let first := SourceSteps.liveFrame original ⟨0,0⟩ 4 valid4
    let ready := SourceSteps.liveFrame first ⟨0,1⟩ 5 (by simpa only [first,SourceSteps.liveFrame,Array.size_set] using valid5)
    let result := LanguageZeroUncached.cachedCaller ready (by simpa only [ready,first,SourceSteps.liveFrame,Array.size_set] using valid5)
    ∃ resultValid : (5 : MIR.LocalId) < result.locals.size,
      (result.locals[5]'resultValid).value = .live (.immediate .uninit) ∧
      (result.locals[5]'resultValid).layout = some RootCompilerFacts.boolLayout := by
  dsimp only
  refine ⟨by simpa only [LanguageZeroUncached.cachedCaller,LocalPlaces.cachePlaceLayout,SourceSteps.liveFrame,Array.size_set] using valid5,?_,?_⟩
  · simp only [LanguageZeroUncached.cachedCaller,LocalPlaces.cachePlaceLayout,SourceSteps.liveFrame,Array.getElem_set_self]
  · simp only [LanguageZeroUncached.cachedCaller,LocalPlaces.cachePlaceLayout,SourceSteps.liveFrame,Array.getElem_set_self]

private theorem four_push_lookup {α : Type} (xs : Array α) (a b c d : α) :
    ((((xs.push a).push b).push c).push d)[xs.size+2]? = some c ∧
    ((((xs.push a).push b).push c).push d)[xs.size]? = some a := by
  constructor <;> simp [Array.getElem_push,Nat.add_assoc]

noncomputable def copyCaller := LanguageZeroUncached.cachedCaller
  (CopyRootGuardEntry.prepared options limits remaining span frames caller machine sourcePointer destinationPointer n input)
  (by rw [CopyRootGuardEntry.prepared_size]; decide)

theorem copy_size : (copyCaller options limits remaining span frames caller machine sourcePointer destinationPointer n input).locals.size = 17 := by
  simp only [copyCaller,LanguageZeroUncached.cachedCaller,LocalPlaces.cachePlaceLayout,Array.size_set]
  exact CopyRootGuardEntry.prepared_size options limits remaining span frames caller machine sourcePointer destinationPointer n input

noncomputable def returnedCopy := ParentFalseReturn.returnedCallerFrame
  (copyCaller options limits remaining span frames caller machine sourcePointer destinationPointer n input)
  (by rw [copy_size]; decide) 1

theorem returned_locals :
    (returnedCopy options limits remaining span frames caller machine sourcePointer destinationPointer n input).locals =
      #[⟨.live (.immediate .uninit),none⟩,
        ⟨.live (.immediate (.scalar sourcePointer)),some CopyCompilerFacts.sourcePointerLayout⟩,
        ⟨.live (.immediate (.scalar destinationPointer)),some CopyCompilerFacts.destPointerLayout⟩,
        ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))),some RootCompilerFacts.usizeLayout⟩,
        ⟨.live (.immediate .uninit),none⟩,
        ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩] ++
        Array.replicate 11 ⟨.dead,none⟩ := by
  have locals := CopyEntryShape.locals
    (Storage.withCurrent frames
      (CopyRootGuardEntry.rootFrame options limits remaining span frames caller machine sourcePointer destinationPointer n input)
      (CopyCallStep.accountedMachine options remaining span machine))
    (LocalPlaces.localRuntimePlace frames.size
      (CopyRootGuardEntry.rootFrame options limits remaining span frames caller machine sourcePointer destinationPointer n input)
      18 CopyHelperUnit.layout).stackView (.goto (some 9) .Continue) input.noRace sourcePointer destinationPointer n
  simp only [returnedCopy,ParentFalseReturn.returnedCallerFrame,copyCaller,LanguageZeroUncached.cachedCaller,
    CopyRootGuardEntry.prepared,SourceSteps.liveFrame,LocalPlaces.cachePlaceLayout]
  change (CopyRootGuardEntry.copyFrame options limits remaining span frames caller machine sourcePointer destinationPointer n input).locals = _ at locals
  simp [locals]
  rfl

private theorem returned_slots (sourcePointer destinationPointer : Scalar Provenance) (n : UInt64)
    (xs : Array (LocalState Provenance LocalLayout))
    (rows : xs = #[⟨.live (.immediate .uninit),none⟩,
        ⟨.live (.immediate (.scalar sourcePointer)),some CopyCompilerFacts.sourcePointerLayout⟩,
        ⟨.live (.immediate (.scalar destinationPointer)),some CopyCompilerFacts.destPointerLayout⟩,
        ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))),some RootCompilerFacts.usizeLayout⟩,
        ⟨.live (.immediate .uninit),none⟩,
        ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩] ++
        Array.replicate 11 ⟨.dead,none⟩) :
    ∃ (v0 : (0 : MIR.LocalId) < xs.size) (v1 : (1 : MIR.LocalId) < xs.size) (v2 : (2 : MIR.LocalId) < xs.size) (v3 : (3 : MIR.LocalId) < xs.size) (v4 : (4 : MIR.LocalId) < xs.size) (v5 : (5 : MIR.LocalId) < xs.size) (v14 : (14 : MIR.LocalId) < xs.size) (v15 : (15 : MIR.LocalId) < xs.size) (v16 : (16 : MIR.LocalId) < xs.size),
      xs[0]'v0 = ⟨.live (.immediate .uninit),none⟩ ∧
      xs[1]'v1 = ⟨.live (.immediate (.scalar sourcePointer)),some CopyCompilerFacts.sourcePointerLayout⟩ ∧
      xs[2]'v2 = ⟨.live (.immediate (.scalar destinationPointer)),some CopyCompilerFacts.destPointerLayout⟩ ∧
      xs[3]'v3 = ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))),some RootCompilerFacts.usizeLayout⟩ ∧
      xs[4]'v4 = ⟨.live (.immediate .uninit),none⟩ ∧
      xs[5]'v5 = ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ ∧
      xs[14]'v14 = ⟨.dead,none⟩ ∧
      xs[15]'v15 = ⟨.dead,none⟩ ∧
      xs[16]'v16 = ⟨.dead,none⟩ := by
  subst xs
  exact ⟨by change 0 < 17; decide,by change 1 < 17; decide,by change 2 < 17; decide,by change 3 < 17; decide,by change 4 < 17; decide,by change 5 < 17; decide,by change 14 < 17; decide,by change 15 < 17; decide,by change 16 < 17; decide,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem returned_metadata :
    let result := returnedCopy options limits remaining span frames caller machine sourcePointer destinationPointer n input
    let root := CopyRootGuardEntry.rootFrame options limits remaining span frames caller machine sourcePointer destinationPointer n input
    result.body = HelperCompilerFacts.copyBody.body ∧
    result.bodyIdentity = HelperCompilerFacts.copyBody.identity ∧
    result.functionInstance = HelperCompilerFacts.copyCall.callee ∧
    result.location = .mir ⟨1,0⟩ ∧ result.locals.size = 17 ∧
    result.returnPlace = (LocalPlaces.localRuntimePlace frames.size root 18 CopyHelperUnit.layout).stackView ∧
    result.returnContinuation = .goto (some 9) .Continue ∧ result.vaList = #[] ∧
    result.extra.dataRace = none ∧ result.extra.borrowTracker = some ({} : FrameState) := by
  dsimp only
  let root := CopyRootGuardEntry.rootFrame options limits remaining span frames caller machine sourcePointer destinationPointer n input
  let state := Storage.withCurrent frames root (CopyCallStep.accountedMachine options remaining span machine)
  let destination := (LocalPlaces.localRuntimePlace frames.size root 18 CopyHelperUnit.layout).stackView
  obtain ⟨body,identity,callee,location,place,continuation,varargs,track⟩ :=
    CopyEntryShape.control state destination (.goto (some 9) .Continue) input.noRace sourcePointer destinationPointer n
  refine ⟨body,identity,callee,rfl,?_,place,continuation,varargs,?_,?_⟩
  · simpa only [returnedCopy,ParentFalseReturn.returnedCallerFrame,Array.size_set] using
      copy_size options limits remaining span frames caller machine sourcePointer destinationPointer n input
  · exact CopyEntryShape.no_clocks state destination (.goto (some 9) .Continue) input.noRace sourcePointer destinationPointer n
  · exact CopyEntryShape.borrow state destination (.goto (some 9) .Continue) input.noRace sourcePointer destinationPointer n
      input.tracker input.tracked

theorem returned_all_immediate : CopyHelperCleanup.AllImmediate
    (returnedCopy options limits remaining span frames caller machine sourcePointer destinationPointer n input) := by
  intro slot member memory
  rw [returned_locals] at member
  simp [Array.mem_def] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

private theorem pushed_active
    (options : EvalConfigurationCore.Options) (state : CanonicalConfigFacts.RootState)
    (destination : RuntimeStackPlace Provenance) (current : CompilerFrameContext.ActualFrame)
    (thread : Miri.Concurrency.ThreadRecord) (active : state.machine.threads.activeThread? = some thread) :
    (LanguageZeroEntry.pushedMachine options state destination current).threads.activeThread? =
      some (PushThread.after thread state.stack.frames.size
        (LanguageZeroEntryFacts.rank options.userRelevantCrates) current.extra.userRelevance) := by
  exact PushThread.active_after (CallEntryFacts.freshRoot state.machine).1 thread state.stack.frames.size
    (LanguageZeroEntryFacts.rank options.userRelevantCrates) current.extra.userRelevance active

private theorem accounted_control (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :
    let h := (PreparedContracts.actualConfig options () (remaining+1) span).terminators
    h.getControl (LanguageZeroStep.accountedMachine options remaining span machine).user =
      TerminatorClock.advance (h.getControl machine.user) := by
  dsimp only
  unfold LanguageZeroStep.accountedMachine PtrMetadataReturn.accountedMachine SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  rfl

theorem from_copy
    (statementFuel : Nat) (statementFuelEq : limits.validation = statementFuel+1)
    (mode : input.tracker.retagMode = .Default) :
    ∃ finalMachine,
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (CopyRootEntry.entered options limits remaining span frames caller machine sourcePointer destinationPointer n input)
        (Storage.withCurrent
          (frames.push (CopyRootGuardEntry.rootFrame options limits remaining span frames caller machine sourcePointer destinationPointer n input))
          (returnedCopy options limits remaining span frames caller machine sourcePointer destinationPointer n input) finalMachine) ∧
      LanguageGuardReturn.Preserves options remaining span machine finalMachine ∧
      ∃ finalThread, finalMachine.threads.activeThread? = some finalThread := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let root := CopyRootGuardEntry.rootFrame options limits remaining span frames caller machine sourcePointer destinationPointer n input
  let copy := copyCaller options limits remaining span frames caller machine sourcePointer destinationPointer n input
  let state := CopyRootGuardEntry.languageState options limits remaining span frames caller machine sourcePointer destinationPointer n input
  let destination := CopyRootGuardEntry.languageDestination options limits remaining span frames caller machine sourcePointer destinationPointer n input
  let frame := LanguageZeroInstalled.frame options state destination
  let pushed := LanguageZeroEntry.pushedMachine options state destination root
  let copyMachine := CopyPushPreserves.post options remaining span machine
  obtain ⟨cm,ct,cth,cr,ca,cg,cv,cb,ce,cty⟩ := CopyPushPreserves.fields options remaining span machine
  obtain ⟨am,atracker,ath,ar,aa,ag,av,ab,ae,aty⟩ := CopyRootGuardState.accounted_fields options remaining span copyMachine
  obtain ⟨pm,pt,pr,pa,pg,pv,pb,pe,pty,pf⟩ := CopyRootGuardState.language_push_fields options state destination root
  have stateTracked : state.machine.borrowTracker = some input.tracker := atracker.trans (ct.trans input.tracked)
  have stateRace : state.machine.dataRace = none := ar.trans (cr.trans input.noRace)
  have stateActive : state.machine.threads.activeThread? = some input.thread := by
    change (LanguageZeroStep.accountedMachine options remaining span copyMachine).threads.activeThread? = _
    rw [ath,cth]
    exact input.active
  have pushedTracked : pushed.borrowTracker = some input.tracker := pt.trans stateTracked
  have pushedRace : pushed.dataRace = none := pr.trans stateRace
  have pushedBackend : pushed.user.payload.payload.user.backend = .none := pb.trans (ab.trans (cb.trans input.backend))
  have pushedGhost : pushed.user.payload.ghost = false := pg.trans (ag.trans (cg.trans input.ghost))
  have pushedValidation : pushed.user.payload.validation = .Shallow := pv.trans (av.trans (cv.trans input.shallow))
  have pushedPreserves : LanguageGuardReturn.Preserves options remaining span machine pushed := {
    memory := pm.trans (am.trans cm),tracker := pt.trans (atracker.trans ct),race := pr.trans (ar.trans cr),
    addresses := pa.trans (aa.trans ca),ghost := pg.trans (ag.trans cg),validation := pv.trans (av.trans cv),
    backend := pb.trans (ab.trans cb),extras := pe.trans (ae.trans ce),types := pty.trans (aty.trans cty),
    fixed := pf.trans (by change (LanguageZeroStep.accountedMachine options remaining span copyMachine).threads.fixedScheduling = _; rw [ath,cth]),
    unchecked := by
      change (config.terminators.getControl (LanguageZeroEntry.pushedMachine options state destination root).user).checkedArithmetic = _
      rw [CopyRootGuardState.language_push_control]
      change (config.terminators.getControl (LanguageZeroStep.accountedMachine options remaining span copyMachine).user).checkedArithmetic = _
      rw [accounted_control,CopyPushPreserves.control]
      rfl,
    noGc := by
      change (config.terminators.getControl (LanguageZeroEntry.pushedMachine options state destination root).user).gcInterval = _
      rw [CopyRootGuardState.language_push_control]
      change (config.terminators.getControl (LanguageZeroStep.accountedMachine options remaining span copyMachine).user).gcInterval = _
      rw [accounted_control,CopyPushPreserves.control]
      rfl }
  have pushedUnchecked : (config.terminators.getControl pushed.user).checkedArithmetic = false := pushedPreserves.unchecked.trans input.unchecked
  have pushedGc : (config.terminators.getControl pushed.user).gcInterval = 0 := pushedPreserves.noGc.trans input.noGc
  have pushedFixed : pushed.threads.fixedScheduling = true := pushedPreserves.fixed.trans input.fixed
  obtain ⟨body,identity,callee,location,track,continuation,varargs⟩ := LanguageZeroInstalled.metadata options state destination
  have size : frame.locals.size = 3 := LanguageZeroInstalled.locals_size options state destination
  have v0 : (0 : MIR.LocalId) < frame.locals.size := by rw [size];decide
  have v1 : (1 : MIR.LocalId) < frame.locals.size := by rw [size];decide
  have v2 : (2 : MIR.LocalId) < frame.locals.size := by rw [size];decide
  obtain ⟨live0,cache0,dead1,cache1,dead2,cache2⟩ := LanguageZeroInstalled.slots options state destination
  change frame.locals[0]?.map (·.value) = some (.live (.immediate .uninit)) at live0
  change frame.locals[0]?.map (·.layout) = some none at cache0
  simp only [Array.getElem?_eq_getElem v0,Option.map_some,Option.some.injEq] at live0 cache0
  change frame.locals[1]?.map (·.value) = some (.dead) at dead1
  change frame.locals[1]?.map (·.layout) = some none at cache1
  simp only [Array.getElem?_eq_getElem v1,Option.map_some,Option.some.injEq] at dead1 cache1
  change frame.locals[2]?.map (·.value) = some (.dead) at dead2
  change frame.locals[2]?.map (·.layout) = some none at cache2
  simp only [Array.getElem?_eq_getElem v2,Option.map_some,Option.some.injEq] at dead2 cache2
  have clocks : frame.extra.dataRace = none := CopyRootGuardState.language_frame_clocks options state destination stateRace
  have borrow : frame.extra.borrowTracker = some ({} : FrameState) :=
    CopyRootGuardState.language_frame_borrow options state destination input.tracker stateTracked
  have original4 : (4 : MIR.LocalId) < (CopyRootGuardEntry.copyFrame options limits remaining span frames caller machine sourcePointer destinationPointer n input).locals.size := by
    rw [CopyRootGuardEntry.copy_size];decide
  have original5 : (5 : MIR.LocalId) < (CopyRootGuardEntry.copyFrame options limits remaining span frames caller machine sourcePointer destinationPointer n input).locals.size := by
    rw [CopyRootGuardEntry.copy_size];decide
  obtain ⟨copyValid5,copyLive5,copyCache5⟩ := prepared_fifth
    (CopyRootGuardEntry.copyFrame options limits remaining span frames caller machine sourcePointer destinationPointer n input) original4 original5
  have copyClocks : copy.extra.dataRace = none := CopyEntryShape.no_clocks
    (Storage.withCurrent frames root (CopyCallStep.accountedMachine options remaining span machine))
    (LocalPlaces.localRuntimePlace frames.size root 18 CopyHelperUnit.layout).stackView
    (.goto (some 9) .Continue) input.noRace sourcePointer destinationPointer n
  have frameDestination : frame.returnPlace.toRuntimePlace =
      LocalPlaces.localRuntimePlace (frames.push root).size copy 5 RootCompilerFacts.boolLayout := by rfl
  let ready := ParentUnitPrelude.afterPrelude frame v1 v2
  have readyValid : (1 : MIR.LocalId) < ready.locals.size := by
    simpa [ready,ParentUnitPrelude.afterPrelude,SourceSteps.liveFrame,LocalPlaces.cachePlaceLayout] using v1
  let runtimeCaller := RuntimeZeroUncached.cachedCaller ready readyValid
  let runtimeState := Storage.withCurrent ((frames.push root).push copy) runtimeCaller
    (RuntimeZeroStep.accountedMachine options remaining span pushed)
  let runtimeDestination := RuntimeZeroEntry.destination ((frames.push root).push copy) ready
  have pushedSize : state.stack.frames.size = frames.size+2 := by
    simp only [state,CopyRootGuardEntry.languageState,Storage.withCurrent,Array.size_push]
  have pushedActive : pushed.threads.activeThread? = some
      (PushThread.after input.thread (frames.size+2) (LanguageZeroEntryFacts.rank options.userRelevantCrates) root.extra.userRelevance) := by
    have active := pushed_active options state destination root input.thread stateActive
    simpa only [pushedSize] using active
  have runtimeMetadata : ∃ (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame),
      pushed.threads.activeThread? = some thread ∧
      FrameRelevance.top (RuntimeZeroEntryFacts.pushed options.userRelevantCrates runtimeState runtimeDestination).stack
        thread.topUserRelevantFrame = some index ∧
      (RuntimeZeroEntryFacts.pushed options.userRelevantCrates runtimeState runtimeDestination).stack.frames[index]? = some current := by
    by_cases rank : LanguageZeroEntryFacts.rank options.userRelevantCrates >= root.extra.userRelevance
    · refine ⟨{input.thread with topUserRelevantFrame := some (frames.size+2)},frames.size+2,runtimeCaller,?_,?_,?_⟩
      · simpa only [PushThread.after,rank,ite_true] using pushedActive
      · simp [FrameRelevance.top]
      · dsimp only [RuntimeZeroEntryFacts.pushed,runtimeState,Storage.withCurrent]
        exact (four_push_lookup frames root copy runtimeCaller _).1
    · refine ⟨input.thread,frames.size,root,?_,?_,?_⟩
      · simpa only [PushThread.after,rank,ite_false] using pushedActive
      · simp [FrameRelevance.top,input.top]
      · dsimp only [RuntimeZeroEntryFacts.pushed,runtimeState,Storage.withCurrent]
        exact (four_push_lookup frames root copy runtimeCaller _).2
  obtain ⟨thread,index,current,active,top,present⟩ := runtimeMetadata
  obtain ⟨finalMachine,bodyTrace,preserved,finalActive,safe⟩ := Language.from_entry
    options limits remaining input.budget input.fuel statementFuel input.budgetEq input.validationFuel statementFuelEq
    span input.source input.cmp input.debug (frames.push root) copy frame pushed body identity callee location size
    v0 live0 cache0 v1 dead1 cache1 v2 dead2 cache2 clocks pushedRace pushedBackend pushedGhost pushedValidation
    input.tracker pushedTracked mode thread index current active top present pushedUnchecked pushedGc pushedFixed
    copyValid5 copyLive5 copyCache5 copyClocks frameDestination 1 .Continue continuation varargs ({} : FrameState) borrow rfl
  have finalPreserves : LanguageGuardReturn.Preserves options remaining span machine finalMachine := {
    memory := preserved.memory.trans pushedPreserves.memory,tracker := preserved.tracker.trans pushedPreserves.tracker,
    race := preserved.race.trans pushedPreserves.race,addresses := preserved.addresses.trans pushedPreserves.addresses,
    ghost := preserved.ghost.trans pushedPreserves.ghost,validation := preserved.validation.trans pushedPreserves.validation,
    backend := preserved.backend.trans pushedPreserves.backend,extras := preserved.extras.trans pushedPreserves.extras,
    types := preserved.types.trans pushedPreserves.types,fixed := preserved.fixed.trans pushedPreserves.fixed,
    unchecked := preserved.unchecked.trans pushedPreserves.unchecked,noGc := preserved.noGc.trans pushedPreserves.noGc }
  refine ⟨finalMachine,?_,finalPreserves,finalActive⟩
  exact SuccessfulTrace.append
    (CopyRootGuardEntry.from_copy options limits remaining span frames caller machine sourcePointer destinationPointer n input) bodyTrace

theorem run
    (statementFuel : Nat) (statementFuelEq : limits.validation = statementFuel+1)
    (mode : input.tracker.retagMode = .Default) :
    ∃ finalMachine,
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent frames caller machine)
        (Storage.withCurrent
          (frames.push (CopyRootGuardEntry.rootFrame options limits remaining span frames caller machine sourcePointer destinationPointer n input))
          (returnedCopy options limits remaining span frames caller machine sourcePointer destinationPointer n input) finalMachine) ∧
      LanguageGuardReturn.Preserves options remaining span machine finalMachine ∧
      ∃ finalThread, finalMachine.threads.activeThread? = some finalThread := by
  obtain ⟨finalMachine,trace,preserved,active⟩ := from_copy options limits remaining span frames caller machine sourcePointer destinationPointer n input statementFuel statementFuelEq mode
  exact ⟨finalMachine,SuccessfulTrace.append (CopyRootEntry.trace options limits remaining span frames caller machine sourcePointer destinationPointer n input) trace,preserved,active⟩

end DuplicatePrefix.CurrentCallCopyGuard

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CurrentCallCopyGuard." || name.toString.startsWith "_private.duplicate_prefix.CurrentCallCopyGuard." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved current copy guard dependency {dependency}"
