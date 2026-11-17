import duplicate_prefix.RuntimeZeroStep
import duplicate_prefix.ParentFalseBranchTail
import duplicate_prefix.SuccessfulTrace

/-! The language guard's actual runtime call, runtime body, false dispatch and
physical false return.  The input describes the language frame before its call;
no successful interpreter operation is an input premise. -/
namespace DuplicatePrefix.LanguageGuardReturn
open Miri Miri.Input Miri.ABI Miri.MIR Miri.Interpreter Miri.Memory Miri.TreeBorrows
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

private theorem accounted_fields (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :
    let next := RuntimeZeroStep.accountedMachine options remaining span machine
    next.memory = machine.memory ∧ next.borrowTracker = machine.borrowTracker ∧
    next.threads = machine.threads ∧ next.dataRace = machine.dataRace ∧
    next.user.addresses = machine.user.addresses ∧
    next.user.payload.ghost = machine.user.payload.ghost ∧
    next.user.payload.validation = machine.user.payload.validation ∧
    next.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
    next.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
    next.user.payload.payload.user.types = machine.user.payload.payload.user.types := by
  unfold RuntimeZeroStep.accountedMachine PtrMetadataReturn.accountedMachine SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  repeat' constructor

set_option autoImplicit false in
/-- State components untouched by a completed guard call.  Terminator counts and
fresh local identities are intentionally absent. -/
structure Preserves
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) : Prop where
  memory : after.memory = before.memory
  tracker : after.borrowTracker = before.borrowTracker
  race : after.dataRace = before.dataRace
  addresses : after.user.addresses = before.user.addresses
  ghost : after.user.payload.ghost = before.user.payload.ghost
  validation : after.user.payload.validation = before.user.payload.validation
  backend : after.user.payload.payload.user.backend = before.user.payload.payload.user.backend
  extras : after.user.payload.payload.user.runtime.extras = before.user.payload.payload.user.runtime.extras
  types : after.user.payload.payload.user.types = before.user.payload.payload.user.types
  fixed : after.threads.fixedScheduling = before.threads.fixedScheduling
  unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl after.user).checkedArithmetic =
    ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl before.user).checkedArithmetic
  noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl after.user).gcInterval =
    ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl before.user).gcInterval

 theorem from_call
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining budget fuel : Nat) (dispatchFuel : limits.callDispatch = budget+1)
    (validationFuel : options.limits.validation = fuel+1)
    (span : PreparedContracts.FixedSpanQuery) (source : PreparedContracts.SourceComparator)
    (cmp : ProjectionMetadataFacts.NullComparator) (debugOff : options.place.debugAssertions = false)
    (frames : Array CompilerFrameContext.ActualFrame) (copy frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = CopyPreconditions.Bodies.checkLanguage.loaded.body)
    (identity : frame.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity)
    (callee : frame.functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance)
    (location : frame.location = .mir ⟨0,3⟩) (size : frame.locals.size = 3)
    (valid0 : (0 : MIR.LocalId) < frame.locals.size)
    (live0 : frame.locals[0].value = .live (.immediate .uninit))
    (uncached0 : frame.locals[0].layout = none)
    (valid1 : (1 : MIR.LocalId) < frame.locals.size)
    (live1 : frame.locals[1].value = .live (.immediate .uninit))
    (uncached1 : frame.locals[1].layout = none)
    (valid2 : (2 : MIR.LocalId) < frame.locals.size)
    (live2 : frame.locals[2].value = .live (.immediate .uninit))
    (layout2 : Option LocalLayout) (cached2 : frame.locals[2].layout = layout2)
    (noClocks : frame.extra.dataRace = none)
    (noRace : machine.dataRace = none) (backend : machine.user.payload.payload.user.backend = .none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .Default)
    (thread : Concurrency.ThreadRecord) (threadIndex : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (RuntimeZeroEntryFacts.pushed options.userRelevantCrates
      (Storage.withCurrent (frames.push copy) (RuntimeZeroUncached.cachedCaller frame valid1)
        (RuntimeZeroStep.accountedMachine options remaining span machine))
      (RuntimeZeroEntry.destination (frames.push copy) frame)).stack
      thread.topUserRelevantFrame = some threadIndex)
    (present : (RuntimeZeroEntryFacts.pushed options.userRelevantCrates
      (Storage.withCurrent (frames.push copy) (RuntimeZeroUncached.cachedCaller frame valid1)
        (RuntimeZeroStep.accountedMachine options remaining span machine))
      (RuntimeZeroEntry.destination (frames.push copy) frame)).stack.frames[threadIndex]? = some current)
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
      Preserves options remaining span machine finalMachine ∧
      ∃ finalThread, finalMachine.threads.activeThread? = some finalThread := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let cached := RuntimeZeroUncached.cachedCaller frame valid1
  let next := RuntimeZeroStep.accountedMachine options remaining span machine
  have step := RuntimeZeroStep.step options limits remaining budget dispatchFuel span source cmp debugOff
    (frames.push copy) frame machine body identity callee location valid1 live1 uncached1 noClocks
    noRace backend ghost tracker tracked thread threadIndex current active top present unchecked noGc fixed
  have cachedSize : cached.locals.size = 3 := by simp [cached,RuntimeZeroUncached.cachedCaller,LocalPlaces.cachePlaceLayout,size]
  have cachedValid0 : (0 : MIR.LocalId) < cached.locals.size := by rw [cachedSize];decide
  have cachedValid1 : (1 : MIR.LocalId) < cached.locals.size := by rw [cachedSize];decide
  have cachedValid2 : (2 : MIR.LocalId) < cached.locals.size := by rw [cachedSize];decide
  have nextFields := accounted_fields options remaining span machine
  have nextUnchecked : (config.terminators.getControl next.user).checkedArithmetic = false := by
    change (config.terminators.getControl (PtrMetadataReturn.accountedMachine options remaining span machine).user).checkedArithmetic = false
    unfold PtrMetadataReturn.accountedMachine SourceControl.accounted
    dsimp only [Storage.withCurrent]
    rw [CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span]
    exact unchecked
  have nextGc : (config.terminators.getControl next.user).gcInterval = 0 := by
    change (config.terminators.getControl (PtrMetadataReturn.accountedMachine options remaining span machine).user).gcInterval = 0
    unfold PtrMetadataReturn.accountedMachine SourceControl.accounted
    dsimp only [Storage.withCurrent]
    rw [CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span]
    exact noGc
  have runtime := RuntimeZeroCallStep.call_runtime_then_parent_false_branch options limits remaining budget fuel
    dispatchFuel validationFuel span source cmp debugOff (frames.push copy) cached next
    body identity callee location cachedValid2 cachedSize cachedValid0
    (by simpa [cached,RuntimeZeroUncached.cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set] using live0)
    (by simpa [cached,RuntimeZeroUncached.cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set] using uncached0)
    cachedValid1
    (by simpa [cached,RuntimeZeroUncached.cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set] using live1)
    (by simp [cached,RuntimeZeroUncached.cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set,valid1])
    (by simpa [cached,RuntimeZeroUncached.cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set] using live2)
    layout2
    (by simpa [cached,RuntimeZeroUncached.cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set] using cached2)
    noClocks noRace (nextFields.2.2.2.2.2.2.2.1.trans backend)
    (nextFields.2.2.2.2.2.1.trans ghost) (nextFields.2.2.2.2.2.2.1.trans shallow)
    tracker tracked mode thread threadIndex current active top present
    (PushThread.after thread ((frames.push copy).push cached).size
      (RuntimeZeroEntryFacts.rank options.userRelevantCrates) current.extra.userRelevance)
    rfl nextUnchecked nextGc fixed
  rcases runtime with ⟨_, afterAssign, afterReturn, deadState, branchState,
    stepAssign, stepReturn, _, stepDead, _, stepBranch, _,
    branchFrame, branchMachine, branchEq, branchBody, branchIdentity, branchCallee, branchLocation, branchSize,
    branch0, branch0Layout, branch1, branch1Layout, branch2, branch2Layout,
    branchClocks, branchTracked, branchRace, branchMode, branchGhost, branchShallow,
    branchUnchecked, branchGc, branchFixed, branchBorrow, branchDestination, branchContinuation, branchVarargs,
    branchMemory, branchAddresses, branchTypes, branchBackend, branchExtras,
    activeThread, branchActive⟩
  have branchValid0 : (0 : MIR.LocalId) < branchFrame.locals.size := by rw [branchSize];decide
  have branchValid1 : (1 : MIR.LocalId) < branchFrame.locals.size := by rw [branchSize];decide
  have branchValid2 : (2 : MIR.LocalId) < branchFrame.locals.size := by rw [branchSize];decide
  have branchLive0 : branchFrame.locals[0].value = .live (.immediate .uninit) := by
    simpa [Array.getElem?_eq_getElem branchValid0] using branch0
  have branchUncached0 : branchFrame.locals[0].layout = none := by
    simpa [Array.getElem?_eq_getElem branchValid0] using branch0Layout
  have branchLive1 : branchFrame.locals[1].value = .live (.immediate (.scalar (.fromBool false))) := by
    simpa [Array.getElem?_eq_getElem branchValid1] using branch1
  have branchCached1 : branchFrame.locals[1].layout = some RootCompilerFacts.boolLayout := by
    simpa [Array.getElem?_eq_getElem branchValid1] using branch1Layout
  have branchDead2 : branchFrame.locals[2].value = .dead := by
    simpa [Array.getElem?_eq_getElem branchValid2] using branch2
  have validAssigned : (1 : MIR.LocalId) < (ParentFalseAssignment.falseReturnFrame branchFrame branchValid0).locals.size := by
    simpa [ParentFalseAssignment.falseReturnFrame,ParentFalseAssignment.cacheReturnLayout,
      LocalPlaces.cachePlaceLayout] using branchValid1
  have direct : ∀ slot ∈ (SourceSteps.deadFrame
      {ParentFalseAssignment.falseReturnFrame branchFrame branchValid0 with location := .mir ⟨4,0⟩}
      ⟨4,0⟩ 1 validAssigned).locals, ∀ memory, slot.value ≠ .live (.indirect memory) := by
    intro slot member memory bad
    obtain ⟨i, bound, equal⟩ := Array.mem_iff_getElem.mp member
    have small : i < 3 := by
      simpa [SourceSteps.deadFrame,ParentFalseAssignment.falseReturnFrame,
        ParentFalseAssignment.cacheReturnLayout,LocalPlaces.cachePlaceLayout,branchSize] using bound
    have cases3 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    have valueEq := congrArg (fun row : LocalState Provenance LocalLayout => row.value) equal
    rw [bad] at valueEq
    rcases cases3 with rfl | rfl | rfl
    all_goals simp [SourceSteps.deadFrame,ParentFalseAssignment.falseReturnFrame,
      ParentFalseAssignment.cacheReturnLayout,LocalPlaces.cachePlaceLayout,
      Array.getElem_set,branchDead2,branchValid0] at valueEq
  have tail := ParentFalseBranchTail.run options limits remaining fuel span source debugOff validationFuel
    (frames.push copy) frames copy branchFrame rfl branchMachine branchBody branchIdentity branchCallee
    branchLocation branchValid0 branchLive0 branchUncached0 branchValid1 branchLive1 branchCached1
    validAssigned branchClocks tracker branchTracked branchMode branchGhost branchShallow
    branchUnchecked branchGc branchFixed copyValid5 copyLive5 copyCached5 copyNoClocks
    (by rw [branchDestination]; exact destination) target unwind (branchContinuation.trans continuation)
    direct (branchVarargs.trans varargs) borrowFrame (branchBorrow.trans frameTracked) empty
    activeThread branchActive
  obtain ⟨afterFalse, afterGoto, afterDead, finalState, stepFalse, stepGoto, stepDrop, stepFinish, finalEq⟩ := tail
  let finalMachine := finalState.machine
  have finalKeep : Preserves options remaining span branchMachine finalMachine := by
    constructor
    all_goals dsimp only [finalMachine]; rw [finalEq]
    all_goals unfold ParentFalseReturn.poppedMachine GenericPopFrame.afterRelevanceAt
    all_goals split
    all_goals dsimp only [GenericPopFrame.afterRelevance,SourceControl.accounted,Storage.withCurrent]
    all_goals simp only [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    all_goals rfl
  have finalActive : ∃ finalThread, finalMachine.threads.activeThread? = some finalThread := by
    dsimp only [finalMachine]
    rw [finalEq]
    apply PopActive.after_relevance_at_active
    exact branchActive
  refine ⟨finalMachine, ?_, ?_, finalActive⟩
  · have endState : finalState = Storage.withCurrent frames
        (ParentFalseReturn.returnedCallerFrame copy copyValid5 target) finalMachine := by
      dsimp only [finalMachine]
      rw [finalEq]
      rfl
    have rest : SuccessfulTrace.Trace config limits branchState
        (Storage.withCurrent frames (ParentFalseReturn.returnedCallerFrame copy copyValid5 target) finalMachine) := by
      rw [branchEq,← endState]
      exact .next stepFalse (.next stepGoto (.next stepDrop (.next stepFinish (.refl _))))
    exact .next step (.next stepAssign (.next stepReturn (.next stepDead (.next stepBranch rest))))
  · exact {
      memory := finalKeep.memory.trans (branchMemory.trans nextFields.1)
      tracker := finalKeep.tracker.trans (branchTracked.trans tracked.symm)
      race := finalKeep.race.trans (branchRace.trans noRace.symm)
      addresses := finalKeep.addresses.trans (branchAddresses.trans nextFields.2.2.2.2.1)
      ghost := finalKeep.ghost.trans (branchGhost.trans ghost.symm)
      validation := finalKeep.validation.trans (branchShallow.trans shallow.symm)
      backend := finalKeep.backend.trans (branchBackend.trans nextFields.2.2.2.2.2.2.2.1)
      extras := finalKeep.extras.trans (branchExtras.trans nextFields.2.2.2.2.2.2.2.2.1)
      types := finalKeep.types.trans (branchTypes.trans nextFields.2.2.2.2.2.2.2.2.2)
      fixed := finalKeep.fixed.trans (branchFixed.trans fixed.symm)
      unchecked := finalKeep.unchecked.trans (branchUnchecked.trans unchecked.symm)
      noGc := finalKeep.noGc.trans (branchGc.trans noGc.symm) }

end DuplicatePrefix.LanguageGuardReturn

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.LanguageGuardReturn.from_call) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved language guard return dependency {dependency}"
