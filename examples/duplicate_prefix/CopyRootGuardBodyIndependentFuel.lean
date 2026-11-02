import duplicate_prefix.CopyRootGuardBody
import duplicate_prefix.CopyRootGuardState
import duplicate_prefix.LanguageGuardBodyIndependentFuel
import duplicate_prefix.CopyRootComplete
import duplicate_prefix.CopyRootOutput

/-! The actual language guard reached by the root's copy call. The runtime
cache metadata is derived from its real push; no guard trace is assumed. -/
namespace DuplicatePrefix.CopyRootGuardBodyIndependentFuel
open DuplicatePrefix.CopyRootGuardBody
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
    (statementBudget : Nat) (statementFuel : limits.validation = statementBudget+1)
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
  obtain ⟨finalMachine,bodyTrace,preserved,finalActive,safe⟩ := LanguageGuardBodyIndependentFuel.from_entry
    options limits remaining input.budget input.fuel input.budgetEq input.validationFuel statementBudget statementFuel
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

end DuplicatePrefix.CopyRootGuardBodyIndependentFuel
