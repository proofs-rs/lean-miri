import duplicate_prefix.RootZeroSwitch
namespace DuplicatePrefix.RootGuardSwitch
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem step
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (boolean : Bool)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (location : frame.location = .mir ⟨4,3⟩)
    (size : frame.locals.size = 25)
    (valid8 : (8 : MIR.LocalId) < frame.locals.size)
    (live8 : (frame.locals[8]'(by omega)).value = .live
      (.immediate (.scalar (.fromBool boolean))))
    (cached8 : (frame.locals[8]'(by omega)).layout = some RootCompilerFacts.boolLayout)
    (noClocks : frame.extra.dataRace = none)
    (ghostFalse : machine.user.payload.ghost = false)
    (checkedArithmetic : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (gcDisabled : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixedScheduling : machine.threads.fixedScheduling = true) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let after := Storage.withCurrent framesBefore
      {frame with location := .mir ⟨if boolean then 5 else 6,0⟩}
      (SourceControl.accounted config.terminators (Storage.withCurrent framesBefore frame machine)).machine
    ExecutionMachine.step config limits () (Storage.withCurrent framesBefore frame machine) =
      (after,.ok true) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let before := Storage.withCurrent framesBefore frame machine
  let accounted := SourceControl.accounted config.terminators before
  have fields := CanonicalConfigFacts.actual_fields options () (remaining+1) span
  have getSet : ∀ control user, config.terminators.getControl (config.terminators.setControl control user) = control := by
    rw [fields.terminators]
    intro control user
    rfl
  have setSet : ∀ first second user,
      config.terminators.setControl second (config.terminators.setControl first user) =
        config.terminators.setControl second user := by
    rw [fields.terminators]
    intro first second user
    rfl
  have noGc := gcDisabled
  have fixed := fixedScheduling
  have unchecked := checkedArithmetic
  have accounting := SourceControl.before_terminator config limits () before getSet setSet unchecked noGc fixed
  have accountedGhost : accounted.machine.user.payload.ghost = false := by
    have ghostEq : (config.terminators.setControl
        (TerminatorClock.advance (config.terminators.getControl machine.user)) machine.user).payload.ghost =
        machine.user.payload.ghost := by
      rw [fields.terminators]
      rfl
    change (config.terminators.setControl
      (TerminatorClock.advance (config.terminators.getControl machine.user)) machine.user).payload.ghost = false
    rw [ghostEq, ghostFalse]
  have validGetter : (ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits)).compiler.validationInProgress accounted =
      .ok false accounted := by
    change config.compiler.validationInProgress accounted = _
    rw [fields.compilerValidationInProgress]
    simp [ValidityMachine.validationInProgress, accountedGhost,
      get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure]
  let block := RootBody.reflected.body.body.basicBlocks[4]'(by with_unfolding_all decide +kernel)
  have blockEq : RootBody.reflected.body.body.basicBlocks[4]? = some block := by simp [block]
  have reflectedKind : block.terminator.kind = .SwitchInt (.Move ⟨8,#[]⟩) ⟨#[.Case 0 6],5⟩ := by with_unfolding_all rfl
  have blockAt : frame.body.basicBlocks[4]? = some block := by
    rw [body]
    exact blockEq
  have kind : block.terminator.kind = .SwitchInt (.Move ⟨8,#[]⟩) ⟨#[.Case 0 6],5⟩ := by
    exact reflectedKind
  have noStatement : block.statements[3]? = none := by
    have reflectedNoStatement : RootBody.reflected.body.body.basicBlocks[4]?.bind
        (fun bb => bb.statements[3]?) = none := by
      rfl
    rw [blockEq] at reflectedNoStatement
    exact reflectedNoStatement
  have current : before.stack.currentFrame? = some frame := by
    simp [before, Storage.withCurrent, Stack.currentFrame?]
  have sized : RootCompilerFacts.boolLayout.layout.backendRepr.isUnsized = false := by decide +kernel
  have initialized : CopyCompilerFacts.initializedScalar RootCompilerFacts.boolLayout = true := by decide +kernel
  obtain ⟨primitive, range, readable⟩ := CopyCompilerFacts.initialized_scalar_exists
    RootCompilerFacts.boolLayout initialized
  let scalar : Scalar Provenance := Scalar.fromBool boolean
  let hooks := ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits)
  let op : OpTy Provenance := ⟨.immediate (.scalar scalar), RootCompilerFacts.boolLayout⟩
  have accountedFrame : accounted = Storage.withCurrent framesBefore frame accounted.machine := by
    rfl
  have getterLocal : hooks.compiler.validationInProgress
      (Storage.withCurrent framesBefore frame accounted.machine) =
      .ok false (Storage.withCurrent framesBefore frame accounted.machine) := by
    change hooks.compiler.validationInProgress accounted = .ok false accounted
    exact validGetter
  have localRead := LocalOperands.cached_immediate hooks () framesBefore frame accounted.machine 8
    (.scalar scalar) RootCompilerFacts.boolLayout none valid8 live8 cached8 sized noClocks
    false getterLocal
  have typeCheck := RootLocalStages.operand_check_skipped options limits () (remaining+1) span
    debugOff (OperandDispatch.wholeLocal 8) op accounted
  have operand := OperandDispatch.evalOperandAt_move_wholeLocal hooks ()
    (OperandPath.instruction "discriminant") 8 none accounted accounted op localRead typeCheck
  have operand' : OperandMachine.evalOperandAt hooks () (OperandPath.instruction "discriminant")
      (.Move ⟨8,#[]⟩) none accounted = .ok op accounted := by
    simpa only [OperandDispatch.wholeLocal] using operand
  have scalarRead := RootLocalStages.canonical_read_scalar options limits (remaining+1) span
    accounted scalar RootCompilerFacts.boolLayout ⟨primitive, range, readable⟩
  have read : MachineHooks.run (do
      PlaceMachine.readImmediate (ExecutionMachine.withValidation config limits).access
        (← OperandMachine.evalOperandAt hooks () (OperandPath.instruction "discriminant")
          (.Move ⟨8,#[]⟩) none)) accounted =
      (accounted,.ok (ScalarOperations.boolImmediate boolean RootCompilerFacts.boolLayout)) := by
    change MachineHooks.run (do
      let value ← OperandMachine.evalOperandAt hooks () (OperandPath.instruction "discriminant")
        (.Move ⟨8,#[]⟩) none
      (ExecutionMachine.rvalueHooks config limits).readImmediate () value) accounted = _
    simp only [MachineHooks.run, Call.run, Bind.bind, EStateM.bind]
    rw [operand']
    exact congrArg (fun result => match result with
      | .ok value after => (after,Except.ok value)
      | .error error after => (after,Except.error error)) scalarRead
  have classify := RootScalarQueries.bool_classification options (remaining+1) span limits
  have boolLayout := RootScalarQueries.bool_layout options (remaining+1) span limits
  have width : RootCompilerFacts.boolLayout.layout.size = Size.ofBytes 1 := by decide +kernel
  have dispatch := BoolSwitch.dispatch config limits () block.terminator (.Move ⟨8,#[]⟩)
    6 5 accounted accounted RootCompilerFacts.boolLayout boolean kind read classify boolLayout width
  have branch : (if boolean == false then 6 else 5) = (if boolean then 5 else 6) := by
    by_cases h : boolean <;> simp [h]
  have effect : (ExecutionMachine.stepHooks config limits).terminator () block.terminator accounted =
      ControlFlow.goToBlock (if boolean then 5 else 6) accounted := by
    simpa only [branch] using dispatch
  let afterFrame := {frame with location := .mir ⟨if boolean then 5 else 6, 0⟩}
  let after := Storage.withCurrent framesBefore afterFrame accounted.machine
  have goToBlockEq : ControlFlow.goToBlock (if boolean then 5 else 6) accounted = (after,.ok ()) := by
    simp [ControlFlow.goToBlock, ControlFlow.setLocation, after, afterFrame,
      accounted, SourceControl.accounted, before, Storage.withCurrent, Stack.currentFrame?]
  have effect' : (ExecutionMachine.stepHooks config limits).terminator () block.terminator accounted = (after,.ok ()) := by
    rw [effect, goToBlockEq]
  have step := StepFacts.step_terminator (ExecutionMachine.stepHooks config limits) () before accounted after
    frame ⟨4,3⟩ block current location blockAt noStatement accounting effect'
  have sourceStep : ExecutionMachine.step config limits () before = (after,.ok true) := by
    simpa [ExecutionMachine.step] using step
  exact sourceStep

#print axioms step
end DuplicatePrefix.RootGuardSwitch
