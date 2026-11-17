import duplicate_prefix.CopyRuntimeGuardStep
import duplicate_prefix.GenericCallReturn
import duplicate_prefix.PrimitiveCallReturn
import duplicate_prefix.GenericPopFrame
import duplicate_prefix.SourceControl

namespace DuplicatePrefix.ParentFalseReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open DuplicatePrefix
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def returnedCallerFrame (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (valid5 : (5 : MIR.LocalId) < caller.locals.size) (target : BasicBlockId) :=
  {caller with
    locals := caller.locals.set 5
      {value := .live (.immediate (.scalar (Scalar.fromBool false))),
       layout := caller.locals[5].layout} valid5,
    location := .mir ⟨target,0⟩}

def poppedMachine (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (index : Nat) :=
  GenericPopFrame.afterRelevanceAt (frames.push caller) frame machine index

theorem popped_user (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (index : Nat) :
    (poppedMachine frames caller frame machine index).user = machine.user := by
  unfold poppedMachine GenericPopFrame.afterRelevanceAt
  split <;> rfl

theorem parent_return_block :
    ∃ block,
      CopyPreconditions.Bodies.checkLanguage.loaded.body.basicBlocks[4]? = some block ∧
      block.statements[1]? = none ∧ block.terminator.kind = .Return ∧ block.cleanup = false := by
  have kind := CopyPreconditions.Bodies.language_guard_branches.2.2.1
  cases h : CopyPreconditions.Bodies.checkLanguage.loaded.body.basicBlocks[4]? with
  | none => simp [CopyPreconditions.Bodies.terminatorKindAt,h] at kind
  | some block =>
    refine ⟨block,rfl,?_,?_,?_⟩
    · have noStatement : (CopyPreconditions.Bodies.checkLanguage.loaded.body.basicBlocks[4]?).bind
          (fun bb => bb.statements[1]?) = none := by with_unfolding_all decide +kernel
      rw [h] at noStatement
      exact noStatement
    · simpa [CopyPreconditions.Bodies.terminatorKindAt,h] using kind
    · have normal : (CopyPreconditions.Bodies.checkLanguage.loaded.body.basicBlocks[4]?).map (·.cleanup) = some false := by
        with_unfolding_all rfl
      rw [h] at normal
      simpa using normal

theorem return_effect [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = CopyPreconditions.Bodies.checkLanguage.loaded.body)
    (identity : frame.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity)
    (callee : frame.functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance)
    (location : frame.location = .mir ⟨4,1⟩)
    (valid0 : (0 : MIR.LocalId) < frame.locals.size)
    (live0 : frame.locals[0].value = .live (.immediate (.scalar (.fromBool false))))
    (cached0 : frame.locals[0].layout = some RootCompilerFacts.boolLayout)
    (noClocks : frame.extra.dataRace = none)
    (callerValid5 : (5 : MIR.LocalId) < caller.locals.size)
    (callerUninit5 : caller.locals[5].value = .live (.immediate .uninit))
    (callerCached5 : caller.locals[5].layout = some RootCompilerFacts.boolLayout)
    (callerNoClocks : caller.extra.dataRace = none)
    (destination : frame.returnPlace.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size caller 5 RootCompilerFacts.boolLayout)
    (target : BasicBlockId) (unwind : UnwindAction)
    (continuation : frame.returnContinuation = .goto (some target) unwind)
    (immediateLocals : ∀ slot ∈ frame.locals, ∀ memory, slot.value ≠ .live (.indirect memory))
    (varargs : frame.vaList = #[])
    (tracker : MachineHooks.BorrowState) (borrowFrame : Miri.TreeBorrows.FrameState)
    (tracked : machine.borrowTracker = some tracker)
    (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (empty : borrowFrame.protectedTags = #[])
    (thread : Miri.Concurrency.ThreadRecord)
    (active : machine.threads.activeThread? = some thread)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ControlFlow.returnFromCurrentFrame (GenericCallReturn.sourceControl config limits) () false
      (Storage.withCurrent (frames.push caller) frame machine) =
      (Storage.withCurrent frames (returnedCallerFrame caller callerValid5 target)
        (poppedMachine frames caller frame machine
          (thread.topUserRelevantFrame.getD (frames.push caller).size)),.ok ()) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let control := GenericCallReturn.sourceControl config limits
  let before := Storage.withCurrent (frames.push caller) frame machine
  let index := thread.topUserRelevantFrame.getD (frames.push caller).size
  let afterPopMachine := poppedMachine frames caller frame machine index
  let afterPop := Storage.withCurrent frames caller afterPopMachine
  let writtenCaller := {caller with locals := (caller.locals.set 5
      {value := .live (.immediate (.scalar (Scalar.fromBool false))),
       layout := caller.locals[5].layout} callerValid5)}
  let afterCopy := Storage.withCurrent frames writtenCaller afterPopMachine
  let result : OpTy Provenance := ⟨.immediate (.scalar (.fromBool false)),RootCompilerFacts.boolLayout⟩
  have getFrame : control.returnOperand () before = (before,.ok result) := by
    exact PrimitiveCallReturn.read_current_return options limits (remaining+1) span
      (frames.push caller) frame machine RootCompilerFacts.boolLayout (.scalar (.fromBool false))
      valid0 live0 cached0 RootGenericBoolWrite.bool_sized noClocks ghost
  have pop : control.popFrame () before = (afterPop,.ok frame) := by
    change MachineHooks.run (TypedMachineBindings.popRaw
      (TypedMachineBindings.retagHooks config.access config.retag)) before = _
    unfold MachineHooks.run Call.run
    rw [GenericPopFrame.pop_empty_active (TypedMachineBindings.retagHooks config.access config.retag)
      (frames.push caller) frame machine tracker borrowFrame tracked frameTracked empty thread active]
    rfl
  have copy : control.copyReturn () result frame.returnPlace afterPop = (afterCopy,.ok ()) := by
    exact PrimitiveCallReturn.copy_bool_return options limits remaining span debugOff fuel validationFuel
      frames caller afterPopMachine 5 .uninit false callerValid5 callerUninit5 callerCached5 callerNoClocks
      (by
        rw [popped_user]
        exact ghost)
      (by
        rw [popped_user]
        exact shallow)
      frame.returnPlace destination
  have accounting := SourceControl.before_terminator config limits () before
    (CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span)
    (CanonicalConfigFacts.actual_term_set_set options () (remaining+1) span) unchecked noGc fixed
  have cleanup := PrimitiveCallReturn.cleanup_immediate_return options limits (remaining+1) span ()
    afterCopy frame (some target) unwind continuation immediateLocals varargs
  obtain ⟨block,blockAt,noStatement,returnKind,normal⟩ := parent_return_block
  have current : before.stack.currentFrame? = some frame := by simp [before,Storage.withCurrent,Stack.currentFrame?]
  have frameAt : frame.body.basicBlocks[4]? = some block := by rw [body]; exact blockAt
  have returned := GenericCallReturn.normal_goto control () before before afterPop afterCopy afterCopy
    frame frame ⟨4,1⟩ block result target unwind current location frameAt normal getFrame pop copy cleanup continuation
  change ControlFlow.returnFromCurrentFrame control () false before = _
  rw [returned]
  exact GenericCallReturn.goto_current frames writtenCaller afterPopMachine target

theorem return_step [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = CopyPreconditions.Bodies.checkLanguage.loaded.body)
    (identity : frame.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity)
    (callee : frame.functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance)
    (location : frame.location = .mir ⟨4,1⟩)
    (valid0 : (0 : MIR.LocalId) < frame.locals.size)
    (live0 : frame.locals[0].value = .live (.immediate (.scalar (.fromBool false))))
    (cached0 : frame.locals[0].layout = some RootCompilerFacts.boolLayout)
    (noClocks : frame.extra.dataRace = none)
    (callerValid5 : (5 : MIR.LocalId) < caller.locals.size)
    (callerUninit5 : caller.locals[5].value = .live (.immediate .uninit))
    (callerCached5 : caller.locals[5].layout = some RootCompilerFacts.boolLayout)
    (callerNoClocks : caller.extra.dataRace = none)
    (destination : frame.returnPlace.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size caller 5 RootCompilerFacts.boolLayout)
    (target : BasicBlockId) (unwind : UnwindAction)
    (continuation : frame.returnContinuation = .goto (some target) unwind)
    (immediateLocals : ∀ slot ∈ frame.locals, ∀ memory, slot.value ≠ .live (.indirect memory))
    (varargs : frame.vaList = #[])
    (tracker : MachineHooks.BorrowState) (borrowFrame : Miri.TreeBorrows.FrameState)
    (tracked : machine.borrowTracker = some tracker)
    (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (empty : borrowFrame.protectedTags = #[])
    (thread : Miri.Concurrency.ThreadRecord)
    (active : machine.threads.activeThread? = some thread)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ExecutionMachine.step config limits () (Storage.withCurrent (frames.push caller) frame machine) =
      (Storage.withCurrent frames (returnedCallerFrame caller callerValid5 target)
        (poppedMachine frames caller frame
          (SourceControl.accounted config.terminators
            (Storage.withCurrent (frames.push caller) frame machine)).machine
          (thread.topUserRelevantFrame.getD (frames.push caller).size)),.ok true) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let before := Storage.withCurrent (frames.push caller) frame machine
  let accounted := SourceControl.accounted config.terminators before
  let accountedMachine := accounted.machine
  have fields := CanonicalConfigFacts.actual_fields options () (remaining+1) span
  have getSet : ∀ control user, config.terminators.getControl (config.terminators.setControl control user) = control := by
    rw [fields.terminators]
    intro control user
    rfl
  have setSet : ∀ first second user,
      config.terminators.setControl second (config.terminators.setControl first user) = config.terminators.setControl second user := by
    rw [fields.terminators]
    intro first second user
    rfl
  have accounting := SourceControl.before_terminator config limits () before getSet setSet unchecked noGc fixed
  have accountedControl : accountedMachine.user =
      config.terminators.setControl (TerminatorClock.advance (config.terminators.getControl machine.user)) machine.user := by
    change (SourceControl.accounted config.terminators before).machine.user = _
    rw [fields.terminators]
    rfl
  have accountedMachineEq : accountedMachine = {machine with user :=
      (config.terminators.setControl
        (TerminatorClock.advance (config.terminators.getControl machine.user)) machine.user)} := by
    change (SourceControl.accounted config.terminators before).machine = _
    simp [SourceControl.accounted,before,Storage.withCurrent]
  have accountedUnchecked : (config.terminators.getControl accountedMachine.user).checkedArithmetic = false := by
    rw [accountedControl,getSet]
    simpa [TerminatorClock.advance] using unchecked
  have accountedNoGc : (config.terminators.getControl accountedMachine.user).gcInterval = 0 := by
    rw [accountedControl,getSet]
    simpa [TerminatorClock.advance] using noGc
  have accountedGhost : accountedMachine.user.payload.ghost = false := by
    rw [accountedControl,fields.terminators]
    exact ghost
  have accountedShallow : accountedMachine.user.payload.validation = .Shallow := by
    rw [accountedControl,fields.terminators]
    exact shallow
  have accountedTracked : accountedMachine.borrowTracker = some tracker := by
    rw [accountedMachineEq]
    exact tracked
  have accountedActive : accountedMachine.threads.activeThread? = some thread := by
    rw [accountedMachineEq]
    exact active
  have accountedFixed : accountedMachine.threads.fixedScheduling = true := by
    rw [accountedMachineEq]
    exact fixed
  have returned := return_effect options limits remaining span debugOff fuel validationFuel frames caller frame
    accountedMachine body identity callee location valid0 live0 cached0 noClocks callerValid5 callerUninit5
    callerCached5 callerNoClocks destination target unwind continuation immediateLocals varargs tracker borrowFrame
    accountedTracked frameTracked empty thread accountedActive accountedUnchecked accountedNoGc accountedFixed
    accountedGhost accountedShallow
  obtain ⟨block,blockAt,noStatement,returnKind,normal⟩ := parent_return_block
  have frameAt : frame.body.basicBlocks[4]? = some block := by rw [body]; exact blockAt
  have current : before.stack.currentFrame? = some frame := by simp [before,Storage.withCurrent,Stack.currentFrame?]
  exact GenericCallReturn.return_step_exact config limits () before accounted
    (Storage.withCurrent frames (returnedCallerFrame caller callerValid5 target)
      (poppedMachine frames caller frame accountedMachine
        (thread.topUserRelevantFrame.getD (frames.push caller).size))) frame ⟨4,1⟩ block
    current location frameAt noStatement returnKind accounting returned

#print axioms return_effect
#print axioms return_step
end DuplicatePrefix.ParentFalseReturn

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.ParentFalseReturn.popped_user,
      ``DuplicatePrefix.ParentFalseReturn.parent_return_block,
      ``DuplicatePrefix.ParentFalseReturn.return_effect,
      ``DuplicatePrefix.ParentFalseReturn.return_step] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError s!"unapproved parent false-return dependency {dependency}"
