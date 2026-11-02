import duplicate_prefix.RootZeroSwitch
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.RootZeroCompleteSwitch
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open RootZeroSwitch
theorem switch_exact
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (n : UInt64)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (location : frame.location = .mir ⟨0,5⟩)
    (size : frame.locals.size = 25)
    (valid4 : (4 : MIR.LocalId) < frame.locals.size)
    (live4 : (frame.locals[4]'(by omega)).value = .live
      (.immediate (.scalar (.fromBool (n == 0)))))
    (cached4 : (frame.locals[4]'(by omega)).layout = some RootCompilerFacts.boolLayout)
    (noClocks : frame.extra.dataRace = none)
    (ghostFalse : machine.user.payload.ghost = false)
    (checkedArithmetic : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (gcDisabled : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixedScheduling : machine.threads.fixedScheduling = true) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ExecutionMachine.step config limits () (Storage.withCurrent framesBefore frame machine) =
      (Storage.withCurrent framesBefore {frame with location := .mir ⟨if n == 0 then 1 else 2,0⟩}
        (SourceControl.accounted config.terminators (Storage.withCurrent framesBefore frame machine)).machine,.ok true) := by
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
  have blockExists : ∃ block, RootBody.reflected.body.body.basicBlocks[0]? = some block ∧
      block.terminator.kind = .SwitchInt (.Move ⟨4,#[]⟩) ⟨#[.Case 0 2],1⟩ := by
    have shape := root_zero_switch_shape
    cases h : RootBody.reflected.body.body.basicBlocks[0]? with
    | none => simp [terminatorKindAt, h] at shape
    | some block =>
      refine ⟨block, rfl, ?_⟩
      simpa [terminatorKindAt, h] using shape
  obtain ⟨block, blockEq, reflectedKind⟩ := blockExists
  have blockAt : frame.body.basicBlocks[0]? = some block := by
    rw [body]
    exact blockEq
  have kind : block.terminator.kind = .SwitchInt (.Move ⟨4,#[]⟩) ⟨#[.Case 0 2],1⟩ := by
    exact reflectedKind
  have noStatement : block.statements[5]? = none := by
    have reflectedNoStatement : RootBody.reflected.body.body.basicBlocks[0]?.bind
        (fun bb => bb.statements[5]?) = none := by
      rfl
    rw [blockEq] at reflectedNoStatement
    exact reflectedNoStatement
  have current : before.stack.currentFrame? = some frame := by
    simp [before, Storage.withCurrent, Stack.currentFrame?]
  have sized : RootCompilerFacts.boolLayout.layout.backendRepr.isUnsized = false := by decide +kernel
  have initialized : CopyCompilerFacts.initializedScalar RootCompilerFacts.boolLayout = true := by decide +kernel
  obtain ⟨primitive, range, readable⟩ := CopyCompilerFacts.initialized_scalar_exists
    RootCompilerFacts.boolLayout initialized
  let scalar : Scalar Provenance := Scalar.fromBool (n == 0)
  let hooks := ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits)
  let op : OpTy Provenance := ⟨.immediate (.scalar scalar), RootCompilerFacts.boolLayout⟩
  have accountedFrame : accounted = Storage.withCurrent framesBefore frame accounted.machine := by
    rfl
  have getterLocal : hooks.compiler.validationInProgress
      (Storage.withCurrent framesBefore frame accounted.machine) =
      .ok false (Storage.withCurrent framesBefore frame accounted.machine) := by
    change hooks.compiler.validationInProgress accounted = .ok false accounted
    exact validGetter
  have localRead := LocalOperands.cached_immediate hooks () framesBefore frame accounted.machine 4
    (.scalar scalar) RootCompilerFacts.boolLayout none valid4 live4 cached4 sized noClocks
    false getterLocal
  have typeCheck := RootLocalStages.operand_check_skipped options limits () (remaining+1) span
    debugOff (OperandDispatch.wholeLocal 4) op accounted
  have operand := OperandDispatch.evalOperandAt_move_wholeLocal hooks ()
    (OperandPath.instruction "discriminant") 4 none accounted accounted op localRead typeCheck
  have operand' : OperandMachine.evalOperandAt hooks () (OperandPath.instruction "discriminant")
      (.Move ⟨4,#[]⟩) none accounted = .ok op accounted := by
    simpa only [OperandDispatch.wholeLocal] using operand
  have scalarRead := RootLocalStages.canonical_read_scalar options limits (remaining+1) span
    accounted scalar RootCompilerFacts.boolLayout ⟨primitive, range, readable⟩
  have read : MachineHooks.run (do
      PlaceMachine.readImmediate (ExecutionMachine.withValidation config limits).access
        (← OperandMachine.evalOperandAt hooks () (OperandPath.instruction "discriminant")
          (.Move ⟨4,#[]⟩) none)) accounted =
      (accounted,.ok (ScalarOperations.boolImmediate (n == 0) RootCompilerFacts.boolLayout)) := by
    change MachineHooks.run (do
      let value ← OperandMachine.evalOperandAt hooks () (OperandPath.instruction "discriminant")
        (.Move ⟨4,#[]⟩) none
      (ExecutionMachine.rvalueHooks config limits).readImmediate () value) accounted = _
    simp only [MachineHooks.run, Call.run, Bind.bind, EStateM.bind]
    rw [operand']
    exact congrArg (fun result => match result with
      | .ok value after => (after,Except.ok value)
      | .error error after => (after,Except.error error)) scalarRead
  have classify := RootScalarQueries.bool_classification options (remaining+1) span limits
  have boolLayout := RootScalarQueries.bool_layout options (remaining+1) span limits
  have width : RootCompilerFacts.boolLayout.layout.size = Size.ofBytes 1 := by decide +kernel
  have dispatch := BoolSwitch.dispatch config limits () block.terminator (.Move ⟨4,#[]⟩)
    2 1 accounted accounted RootCompilerFacts.boolLayout (n == 0) kind read classify boolLayout width
  have branch : (if (n == 0) == false then 2 else 1) = (if n == 0 then 1 else 2) := by
    by_cases h : n == 0 <;> simp [h]
  have effect : (ExecutionMachine.stepHooks config limits).terminator () block.terminator accounted =
      ControlFlow.goToBlock (if n == 0 then 1 else 2) accounted := by
    simpa [branch] using dispatch
  let afterFrame := {frame with location := .mir ⟨if n == 0 then 1 else 2, 0⟩}
  let after := Storage.withCurrent framesBefore afterFrame accounted.machine
  have goToBlockEq : ControlFlow.goToBlock (if n == 0 then 1 else 2) accounted = (after,.ok ()) := by
    simp [ControlFlow.goToBlock, ControlFlow.setLocation, after, afterFrame,
      accounted, SourceControl.accounted, before, Storage.withCurrent, Stack.currentFrame?]
  have effect' : (ExecutionMachine.stepHooks config limits).terminator () block.terminator accounted = (after,.ok ()) := by
    rw [effect, goToBlockEq]
  have step := StepFacts.step_terminator (ExecutionMachine.stepHooks config limits) () before accounted after
    frame ⟨0,5⟩ block current location blockAt noStatement accounting effect'
  have sourceStep : ExecutionMachine.step config limits () before = (after,.ok true) := by
    simpa [ExecutionMachine.step] using step
  exact sourceStep

#print axioms switch_exact
end DuplicatePrefix.RootZeroCompleteSwitch
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.RootZeroCompleteSwitch.switch_exact) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved exact root zero switch dependency {dependency}"
