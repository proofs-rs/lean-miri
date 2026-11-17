import duplicate_prefix.LanguageGuardReturn
import duplicate_prefix.ParentUnitPrelude

/-! Complete actual body of the language guard, from its first StorageLive
through the nested runtime guard and physical false return. -/
namespace DuplicatePrefix.LanguageGuardBody
open Miri Miri.Input Miri.ABI Miri.MIR Miri.Interpreter Miri.Memory Miri.TreeBorrows
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable def safetyContext [DecidableEq MiriMemoryKind] (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) :
    CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit :=
  ⟨PreparedContracts.actualConfig options () (remaining+1) span,limits,fun _ _ => True⟩

 theorem from_entry
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining budget fuel : Nat) (dispatchFuel : limits.callDispatch = budget+1)
    (validationFuel : options.limits.validation = fuel+1)
    (statementFuel : limits.validation = fuel+1)
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
      CallSafety.NoUBBeforeReturn (safetyContext options limits remaining span) (frames.size+2)
        (Storage.withCurrent (frames.push copy) frame machine) := by
  let ready := ParentUnitPrelude.afterPrelude frame valid1 valid2
  have readySize : ready.locals.size = 3 := by
    simp [ready,ParentUnitPrelude.afterPrelude,SourceSteps.liveFrame,LocalPlaces.cachePlaceLayout,size]
  have readyValid0 : (0 : MIR.LocalId) < ready.locals.size := by rw [readySize];decide
  have readyValid1 : (1 : MIR.LocalId) < ready.locals.size := by rw [readySize];decide
  have readyValid2 : (2 : MIR.LocalId) < ready.locals.size := by rw [readySize];decide
  have first := ParentUnitPrelude.actual_parent_three_statement_steps_exact options limits remaining span
    debugOff fuel statementFuel (frames.push copy) frame machine valid1 valid2 body identity callee location
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
  have safe := SuccessfulTrace.no_ub (safetyContext options limits remaining span) (frames.size+2)
    (Storage.withCurrent (frames.push copy) frame machine)
    (Storage.withCurrent frames (ParentFalseReturn.returnedCallerFrame copy copyValid5 target) finalMachine)
    (by simp [CallSafety.IsCallEntry,CallSafety.frameDepth,Storage.withCurrent])
    fullTrace
    (by simp [CallSafety.pastCallBoundary,CallSafety.frameDepth,Storage.withCurrent])
  exact ⟨finalMachine,fullTrace,preserves,finalActive,safe⟩

end DuplicatePrefix.LanguageGuardBody

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.LanguageGuardBody.from_entry) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved language guard body dependency {dependency}"
