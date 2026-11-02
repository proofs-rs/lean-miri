import duplicate_prefix.RuntimeZeroEntry
import duplicate_prefix.CopyRuntimeGuardStep
import duplicate_prefix.PushThread
import duplicate_prefix.PopActive

/-! The actual zero-argument runtime helper frame executes the real `!true`
    assignment and return.  Call setup is stated alongside the two source
    steps, so callers can compose this with the surrounding call terminator. -/
namespace DuplicatePrefix.RuntimeZeroReturn
open Miri Miri.ABI Miri.Input Miri.MIR Miri.Interpreter Miri.Memory Miri.TreeBorrows
open DuplicatePrefix
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def entryFrame (options : EvalConfigurationCore.Options) (state : CanonicalConfigFacts.RootState)
    (dest : RuntimeStackPlace Provenance) :=
  RuntimeZeroDone.doneFrame (RuntimeZeroEntryFacts.rawFrame options.userRelevantCrates
    (CallEntryFacts.freshRoot state.machine).1 dest (CallEntryFacts.freshRoot state.machine).2)

def entryMachine (options : EvalConfigurationCore.Options) (state : CanonicalConfigFacts.RootState)
    (dest : RuntimeStackPlace Provenance) (current : Frame Provenance LocalLayout MachineHooks.FrameExtra) :=
  (RuntimeZeroEntryFacts.completed options.userRelevantCrates state dest current).machine

def returnedState (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (callerValid1 : (1 : Miri.MIR.LocalId) < caller.locals.size)
    (runtimeFrame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (index : Nat) :=
  Storage.withCurrent frames (CopyRuntimeGuardStep.returnedCallerFrame caller callerValid1 1)
    (CopyRuntimeGuardStep.returnedRuntimeMachine frames caller runtimeFrame machine index)

theorem entry_locals_size (options : EvalConfigurationCore.Options)
    (state : CanonicalConfigFacts.RootState) (dest : RuntimeStackPlace Provenance) :
    (entryFrame options state dest).locals.size = 1 := by
  dsimp [entryFrame, RuntimeZeroEntryFacts.rawFrame, CallEntryFacts.freshRoot,
    RuntimeZeroDone.doneFrame, RuntimeZeroDone.liveSlot, CallEntryFacts.liveSlot,
    Storage.withCurrent, Frame.create]
  with_unfolding_all rfl

theorem entry_local0_valid (options : EvalConfigurationCore.Options)
    (state : CanonicalConfigFacts.RootState) (dest : RuntimeStackPlace Provenance) :
    (0 : Miri.MIR.LocalId) < (entryFrame options state dest).locals.size := by
  rw [entry_locals_size]
  decide

theorem actual_entry_then_body_returns_false
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localValid : 1 < caller.locals.size)
    (localLive : caller.locals[1].value = .live (.immediate .uninit))
    (localCached : caller.locals[1].layout = some RootCompilerFacts.boolLayout)
    (callerNoClocks : caller.extra.dataRace = none) (noRace : machine.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (thread : Concurrency.ThreadRecord) (index : Nat)
    (current : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (RuntimeZeroEntryFacts.pushed options.userRelevantCrates
      (Storage.withCurrent frames caller machine) (RuntimeZeroEntry.destination frames caller)).stack
        thread.topUserRelevantFrame = some index)
    (present : (RuntimeZeroEntryFacts.pushed options.userRelevantCrates
      (Storage.withCurrent frames caller machine) (RuntimeZeroEntry.destination frames caller)).stack.frames[index]? = some current)
    (threadAfter : Concurrency.ThreadRecord)
    (threadAfterEq : threadAfter = PushThread.after thread (frames.push caller).size
      (RuntimeZeroEntryFacts.rank options.userRelevantCrates) current.extra.userRelevance)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    :
    Call.initStackFrame
      (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits) ()
      GuardCompilerFacts.runtimeCall.callee CopyPreconditions.Bodies.languageRuntime.loaded
      GuardCompilerFacts.languageAbi #[] false (RuntimeZeroEntry.destination frames caller)
      (.goto (some 1) .Continue) (Storage.withCurrent frames caller machine) =
      .ok () (Storage.withCurrent (frames.push caller)
        (entryFrame options (Storage.withCurrent frames caller machine)
          (RuntimeZeroEntry.destination frames caller))
        (entryMachine options (Storage.withCurrent frames caller machine)
          (RuntimeZeroEntry.destination frames caller) current)) ∧
    ∃ afterAssign afterReturn,
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining + 1) span) limits ()
        (Storage.withCurrent (frames.push caller)
          (entryFrame options (Storage.withCurrent frames caller machine)
            (RuntimeZeroEntry.destination frames caller))
          (entryMachine options (Storage.withCurrent frames caller machine)
            (RuntimeZeroEntry.destination frames caller) current)) = (afterAssign, .ok true) ∧
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining + 1) span) limits ()
        afterAssign = (afterReturn, .ok true) ∧
      afterReturn = returnedState frames caller (by omega)
        (CopyRuntimeGuardStep.runtimeAfterAssign
          (entryFrame options (Storage.withCurrent frames caller machine) (RuntimeZeroEntry.destination frames caller))
          (entry_local0_valid options (Storage.withCurrent frames caller machine)
            (RuntimeZeroEntry.destination frames caller)))
        ((SourceControl.accounted (PreparedContracts.actualConfig options () (remaining + 1) span).terminators
          (Storage.withCurrent (frames.push caller)
            (CopyRuntimeGuardStep.runtimeAfterAssign
              (entryFrame options (Storage.withCurrent frames caller machine) (RuntimeZeroEntry.destination frames caller))
              (entry_local0_valid options (Storage.withCurrent frames caller machine)
                (RuntimeZeroEntry.destination frames caller)))
            (entryMachine options (Storage.withCurrent frames caller machine)
              (RuntimeZeroEntry.destination frames caller) current))).machine)
        (threadAfter.topUserRelevantFrame.getD (frames.push caller).size) ∧
      afterReturn.machine.user.payload.ghost = false ∧
      ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl
        afterReturn.machine.user).checkedArithmetic = false ∧
      ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl
        afterReturn.machine.user).gcInterval = 0 ∧
      afterReturn.machine.threads.fixedScheduling = true ∧
      afterReturn.machine.borrowTracker = some tracker ∧
      afterReturn.machine.dataRace = none ∧
      afterReturn.machine.user.payload.validation = .Shallow ∧
      ∃ finalThread, afterReturn.machine.threads.activeThread? = some finalThread := by
  let state := Storage.withCurrent frames caller machine
  let dest := RuntimeZeroEntry.destination frames caller
  let frame := entryFrame options state dest
  let post := entryMachine options state dest current
  have entry := RuntimeZeroEntry.actual_entry options limits remaining span debugOff frames caller machine
    localValid localLive localCached callerNoClocks noRace ghost tracker tracked thread index current active top present
  have freshActive : (CallEntryFacts.freshRoot state.machine).1.threads.activeThread? = some thread := by
    change machine.threads.activeThread? = some thread
    exact active
  have postActive : post.threads.activeThread? = some threadAfter := by
    rw [threadAfterEq]
    change (GenericPushRelevance.afterPush (CallEntryFacts.freshRoot state.machine).1
      (frames.push caller).size (RuntimeZeroEntryFacts.rank options.userRelevantCrates)
      current.extra.userRelevance).threads.activeThread? = _
    exact PushThread.active_after (CallEntryFacts.freshRoot state.machine).1 thread
      (frames.push caller).size (RuntimeZeroEntryFacts.rank options.userRelevantCrates)
      current.extra.userRelevance freshActive
  have postNoRace : post.dataRace = none := by
    change (GenericPushRelevance.afterPush (CallEntryFacts.freshRoot state.machine).1
      (frames.push caller).size (RuntimeZeroEntryFacts.rank options.userRelevantCrates)
      current.extra.userRelevance).dataRace = none
    unfold GenericPushRelevance.afterPush
    split <;> simp [CallEntryFacts.cacheTop, CallEntryFacts.freshRoot, state, Storage.withCurrent, noRace]
  have postTracked : post.borrowTracker = some tracker := by
    change (GenericPushRelevance.afterPush (CallEntryFacts.freshRoot state.machine).1
      (frames.push caller).size (RuntimeZeroEntryFacts.rank options.userRelevantCrates)
      current.extra.userRelevance).borrowTracker = some tracker
    unfold GenericPushRelevance.afterPush
    split <;> simp [CallEntryFacts.cacheTop, CallEntryFacts.freshRoot, state, Storage.withCurrent, tracked]
  have postFixed : post.threads.fixedScheduling = true := by
    change (GenericPushRelevance.afterPush (CallEntryFacts.freshRoot state.machine).1
      (frames.push caller).size (RuntimeZeroEntryFacts.rank options.userRelevantCrates)
      current.extra.userRelevance).threads.fixedScheduling = true
    unfold GenericPushRelevance.afterPush
    split <;> simp [CallEntryFacts.cacheTop, CallEntryFacts.freshRoot, state, Storage.withCurrent, fixed]
  have postGhost : post.user.payload.ghost = false := by
    change (GenericPushRelevance.afterPush (CallEntryFacts.freshRoot state.machine).1
      (frames.push caller).size (RuntimeZeroEntryFacts.rank options.userRelevantCrates)
      current.extra.userRelevance).user.payload.ghost = false
    unfold GenericPushRelevance.afterPush
    split <;> simp [CallEntryFacts.cacheTop, CallEntryFacts.freshRoot, state, Storage.withCurrent,
      EvalConfiguration.identity, ghost]
  have postShallow : post.user.payload.validation = .Shallow := by
    change (GenericPushRelevance.afterPush (CallEntryFacts.freshRoot state.machine).1
      (frames.push caller).size (RuntimeZeroEntryFacts.rank options.userRelevantCrates)
      current.extra.userRelevance).user.payload.validation = .Shallow
    unfold GenericPushRelevance.afterPush
    split <;> simp [CallEntryFacts.cacheTop, CallEntryFacts.freshRoot, state, Storage.withCurrent,
      EvalConfiguration.identity, shallow]
  have fields := CanonicalConfigFacts.actual_fields options () (remaining + 1) span
  let config := PreparedContracts.actualConfig options () (remaining + 1) span
  have freshControl : config.terminators.getControl (CallEntryFacts.freshRoot state.machine).1.user =
      config.terminators.getControl machine.user := by
    rw [fields.terminators]
    simp [CallEntryFacts.freshRoot, state, Storage.withCurrent, EvalConfiguration.identity]
    rfl
  have postControl : config.terminators.getControl post.user =
      config.terminators.getControl (CallEntryFacts.freshRoot state.machine).1.user := by
    change config.terminators.getControl
      (GenericPushRelevance.afterPush (CallEntryFacts.freshRoot state.machine).1
        (frames.push caller).size (RuntimeZeroEntryFacts.rank options.userRelevantCrates)
        current.extra.userRelevance).user = _
    unfold GenericPushRelevance.afterPush
    split <;> rfl
  have postUnchecked : ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl post.user).checkedArithmetic = false := by
    rw [postControl, freshControl]
    exact unchecked
  have postNoGc : ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl post.user).gcInterval = 0 := by
    rw [postControl, freshControl]
    exact noGc
  have frameBody : frame.body = CopyPreconditions.Bodies.languageRuntime.loaded.body := by
    simp [frame, entryFrame, RuntimeZeroEntryFacts.rawFrame, CallEntryFacts.freshRoot,
      RuntimeZeroDone.doneFrame, RuntimeZeroDone.liveSlot, CallEntryFacts.liveSlot,
      state, dest, Storage.withCurrent, Frame.create]
  have frameIdentity : frame.bodyIdentity = CopyPreconditions.Bodies.languageRuntime.loaded.identity := by
    simp [frame, entryFrame, RuntimeZeroEntryFacts.rawFrame, CallEntryFacts.freshRoot,
      RuntimeZeroDone.doneFrame, RuntimeZeroDone.liveSlot, CallEntryFacts.liveSlot,
      state, dest, Storage.withCurrent, Frame.create]
  have frameCallee : frame.functionInstance = CopyPreconditions.Bodies.languageRuntime.fnInstance := by
    change GuardCompilerFacts.runtimeCall.callee = CopyPreconditions.Bodies.languageRuntime.fnInstance
    exact GuardCompilerFacts.runtime_callee
  have frameLocation : frame.location = .mir ⟨0,0⟩ := by
    simpa [frame, entryFrame, RuntimeZeroEntryFacts.rawFrame, CallEntryFacts.freshRoot,
      RuntimeZeroDone.doneFrame, RuntimeZeroDone.liveSlot, CallEntryFacts.liveSlot,
      state, dest, Storage.withCurrent, Frame.create, MIR.Location.start]
      using (show (MIR.Location.start : MIR.Location) = ⟨0,0⟩ by decide +kernel)
  have frameSize : frame.locals.size = 1 := by
    dsimp [frame, entryFrame, RuntimeZeroEntryFacts.rawFrame, CallEntryFacts.freshRoot,
      RuntimeZeroDone.doneFrame, RuntimeZeroDone.liveSlot, CallEntryFacts.liveSlot,
      state, dest, Storage.withCurrent, Frame.create]
    with_unfolding_all rfl
  have valid0 : (0 : Miri.MIR.LocalId) < frame.locals.size := by rw [frameSize]; decide
  have uninit0 : (frame.locals[0]'valid0).value = .live (.immediate .uninit) := by
    simp [frame, entryFrame, RuntimeZeroDone.doneFrame, RuntimeZeroDone.liveSlot,
      CallEntryFacts.liveSlot, RuntimeZeroEntryFacts.rawFrame, CallEntryFacts.freshRoot,
      state, dest, Storage.withCurrent, Frame.create, valid0, Array.getElem_modify]
  have uncached0 : (frame.locals[0]'valid0).layout = none := by
    simp [frame, entryFrame, RuntimeZeroDone.doneFrame, RuntimeZeroDone.liveSlot,
      CallEntryFacts.liveSlot, RuntimeZeroEntryFacts.rawFrame, CallEntryFacts.freshRoot,
      state, dest, Storage.withCurrent, Frame.create, valid0, Array.getElem_modify]
  have frameNoClocks : frame.extra.dataRace = none := by
    simp [frame, entryFrame, RuntimeZeroDone.doneFrame, RuntimeZeroEntryFacts.rawFrame,
      RuntimeZeroDone.liveSlot, CallEntryFacts.liveSlot, CallEntryFacts.freshRoot,
      state, dest, Storage.withCurrent, noRace]
  have frameTracked : frame.extra.borrowTracker = some ({} : FrameState) := by
    simp [frame, entryFrame, RuntimeZeroDone.doneFrame, RuntimeZeroDone.liveSlot,
      CallEntryFacts.liveSlot, RuntimeZeroEntryFacts.rawFrame,
      CallEntryFacts.freshRoot, state, dest, Storage.withCurrent, tracked]
  have frameVarargs : frame.vaList = #[] := by
    simp [frame, entryFrame, RuntimeZeroDone.doneFrame, RuntimeZeroDone.liveSlot,
      CallEntryFacts.liveSlot, RuntimeZeroEntryFacts.rawFrame,
      CallEntryFacts.freshRoot, state, dest, Storage.withCurrent, Frame.create]
  have callerValid : (1 : Miri.MIR.LocalId) < caller.locals.size := localValid
  have callerUninit : (caller.locals[1]'callerValid).value = .live (.immediate .uninit) := localLive
  have callerCache : (caller.locals[1]'callerValid).layout = some RootCompilerFacts.boolLayout := localCached
  have returnDest : frame.returnPlace.toRuntimePlace =
      LocalPlaces.localRuntimePlace frames.size caller 1 RootCompilerFacts.boolLayout := by
    change (LocalPlaces.localRuntimePlace frames.size caller 1 RootCompilerFacts.boolLayout).stackView.toRuntimePlace = _
    exact RuntimePlace.stackView_toRuntimePlace _
  have continuation : frame.returnContinuation = .goto (some 1) .Continue := by
    simp only [frame, entryFrame, RuntimeZeroDone.doneFrame, RuntimeZeroDone.liveSlot,
      CallEntryFacts.liveSlot, RuntimeZeroEntryFacts.rawFrame, CallEntryFacts.freshRoot,
      state, dest, Storage.withCurrent, Frame.create]
  have callerSize : caller.locals.size > 1 := by omega
  have emptyBorrow : ({} : FrameState).protectedTags = #[] := rfl
  have first := CopyRuntimeGuardStep.actual_runtime_body_returns_false
    options limits remaining span source debugOff fuel validationFuel frames caller frame post
    frameBody frameIdentity frameCallee frameLocation valid0 uninit0 uncached0 frameNoClocks
    callerValid callerUninit callerCache callerNoClocks returnDest 1 .Continue continuation
    frameSize callerSize frameVarargs tracker ({} : FrameState) postTracked frameTracked
    emptyBorrow threadAfter postActive postUnchecked postNoGc postFixed postGhost postShallow
  refine ⟨?_, ?_⟩
  · change Call.initStackFrame
      (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits) ()
      GuardCompilerFacts.runtimeCall.callee CopyPreconditions.Bodies.languageRuntime.loaded
      GuardCompilerFacts.languageAbi #[] false dest (.goto (some 1) .Continue) state =
      .ok () (Storage.withCurrent (frames.push caller) (entryFrame options state dest)
        (entryMachine options state dest current))
    exact entry
  obtain ⟨afterAssign, stepAssign, stepReturn⟩ := first
  let afterFrame := CopyRuntimeGuardStep.runtimeAfterAssign frame valid0
  let accounted := SourceControl.accounted (PreparedContracts.actualConfig options () (remaining + 1) span).terminators
    (Storage.withCurrent (frames.push caller) afterFrame post)
  let afterReturnState : MachineHooks.State MiriMemoryKind Machine.RootUser :=
    Storage.withCurrent frames (CopyRuntimeGuardStep.returnedCallerFrame caller callerValid 1)
      (CopyRuntimeGuardStep.returnedRuntimeMachine frames caller afterFrame accounted.machine
        (threadAfter.topUserRelevantFrame.getD (frames.push caller).size))
  refine ⟨afterAssign, afterReturnState, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining + 1) span) limits ()
      (Storage.withCurrent (frames.push caller) frame post) = (afterAssign, .ok true)
    exact stepAssign
  · exact stepReturn
  · simp [afterReturnState, returnedState, afterFrame, accounted, frame, post, state, dest, entryMachine]
  · have accountedGhost : accounted.machine.user.payload.ghost = post.user.payload.ghost := by
      dsimp [accounted, SourceControl.accounted]
      rw [fields.terminators]
      rfl
    have returnedGhost : afterReturnState.machine.user.payload.ghost = post.user.payload.ghost := by
      change (CopyRuntimeGuardStep.returnedRuntimeMachine frames caller afterFrame accounted.machine
        (threadAfter.topUserRelevantFrame.getD (frames.push caller).size)).user.payload.ghost = _
      rw [CopyRuntimeGuardStep.returnedRuntimeMachine_user, accountedGhost]
    rw [returnedGhost, postGhost]
  · have accountedControl : (PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl
        accounted.machine.user = TerminatorClock.advance
          ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl post.user) := by
      dsimp [accounted, SourceControl.accounted]
      rw [fields.terminators]
      rfl
    have returnedControl : (PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl
        afterReturnState.machine.user =
        (PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl accounted.machine.user := by
      change (PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl
        (CopyRuntimeGuardStep.returnedRuntimeMachine frames caller afterFrame accounted.machine
          (threadAfter.topUserRelevantFrame.getD (frames.push caller).size)).user = _
      rw [CopyRuntimeGuardStep.returnedRuntimeMachine_user]
    rw [returnedControl, accountedControl, TerminatorClock.advance]
    exact postUnchecked
  · have accountedControl : (PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl
        accounted.machine.user = TerminatorClock.advance
          ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl post.user) := by
      dsimp [accounted, SourceControl.accounted]
      rw [fields.terminators]
      rfl
    have returnedControl : (PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl
        afterReturnState.machine.user =
        (PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl accounted.machine.user := by
      change (PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl
        (CopyRuntimeGuardStep.returnedRuntimeMachine frames caller afterFrame accounted.machine
          (threadAfter.topUserRelevantFrame.getD (frames.push caller).size)).user = _
      rw [CopyRuntimeGuardStep.returnedRuntimeMachine_user]
    rw [returnedControl, accountedControl, TerminatorClock.advance]
    exact postNoGc
  · have accountedFixed : accounted.machine.threads.fixedScheduling = post.threads.fixedScheduling := rfl
    have returnedFixed : afterReturnState.machine.threads.fixedScheduling = accounted.machine.threads.fixedScheduling := by
      change (CopyRuntimeGuardStep.returnedRuntimeMachine frames caller afterFrame accounted.machine
        (threadAfter.topUserRelevantFrame.getD (frames.push caller).size)).threads.fixedScheduling = _
      unfold CopyRuntimeGuardStep.returnedRuntimeMachine GenericPopFrame.afterRelevanceAt
      split <;> rfl
    rw [returnedFixed, accountedFixed, postFixed]
  · have accountedTracked : accounted.machine.borrowTracker = post.borrowTracker := by
      dsimp [accounted, SourceControl.accounted]
      rfl
    have returnedTracked : afterReturnState.machine.borrowTracker = accounted.machine.borrowTracker := by
      change (CopyRuntimeGuardStep.returnedRuntimeMachine frames caller afterFrame accounted.machine
        (threadAfter.topUserRelevantFrame.getD (frames.push caller).size)).borrowTracker = _
      unfold CopyRuntimeGuardStep.returnedRuntimeMachine GenericPopFrame.afterRelevanceAt
      split <;> rfl
    rw [returnedTracked, accountedTracked, postTracked]
  · have accountedNoRace : accounted.machine.dataRace = post.dataRace := by
      dsimp [accounted, SourceControl.accounted]
      rfl
    have returnedNoRace : afterReturnState.machine.dataRace = accounted.machine.dataRace := by
      change (CopyRuntimeGuardStep.returnedRuntimeMachine frames caller afterFrame accounted.machine
        (threadAfter.topUserRelevantFrame.getD (frames.push caller).size)).dataRace = _
      unfold CopyRuntimeGuardStep.returnedRuntimeMachine GenericPopFrame.afterRelevanceAt
      split <;> rfl
    rw [returnedNoRace,accountedNoRace,postNoRace]
  · have accountedShallow : accounted.machine.user.payload.validation = post.user.payload.validation := by
      dsimp [accounted, SourceControl.accounted]
      rw [fields.terminators]
      rfl
    have returnedShallow : afterReturnState.machine.user.payload.validation = accounted.machine.user.payload.validation := by
      change (CopyRuntimeGuardStep.returnedRuntimeMachine frames caller afterFrame accounted.machine
        (threadAfter.topUserRelevantFrame.getD (frames.push caller).size)).user.payload.validation = _
      rw [CopyRuntimeGuardStep.returnedRuntimeMachine_user]
    rw [returnedShallow,accountedShallow,postShallow]
  · have accountedActive : accounted.machine.threads.activeThread? = some threadAfter := by
      dsimp [accounted, SourceControl.accounted]
      exact postActive
    obtain ⟨finalThread, activeFinal⟩ :=
      PopActive.after_relevance_at_active (frames.push caller) afterFrame accounted.machine
        (threadAfter.topUserRelevantFrame.getD (frames.push caller).size) threadAfter accountedActive
    exact ⟨finalThread, by
      change (CopyRuntimeGuardStep.returnedRuntimeMachine frames caller afterFrame accounted.machine
        (threadAfter.topUserRelevantFrame.getD (frames.push caller).size)).threads.activeThread? = _
      exact activeFinal⟩

end
end DuplicatePrefix.RuntimeZeroReturn

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.RuntimeZeroReturn.actual_entry_then_body_returns_false) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved actual runtime call/body/return dependency {dependency}"
