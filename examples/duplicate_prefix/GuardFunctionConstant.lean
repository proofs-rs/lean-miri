import duplicate_prefix.GuardCompilerFacts
import duplicate_prefix.RootCompilerFacts

/-! Actual MIR constant for the outer copy-wrapper call to `check_language_ub`.
This mirrors the inner runtime-call operand using the production compiler
constant evaluator at the reflected source location. -/
namespace DuplicatePrefix.GuardFunctionConstant
noncomputable section
open Miri Miri.ABI Miri.Input Miri.MIR Miri.Interpreter Miri.Memory
open DuplicatePrefix
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

private def checkedOk {Error Value : Type} : (result : Except Error Value) → result.isOk = true → Value
  | .ok value, _ => value
  | .error _, impossible => False.elim (by cases impossible)
private theorem checkedOk_eq {Error Value : Type} (result : Except Error Value)
    (supported : result.isOk = true) : result = .ok (checkedOk result supported) := by
  cases result with
  | ok value => rfl
  | error reason => cases supported

def constant : ConstOperand := ⟨⟨66⟩, none, .Val .ZeroSized 206⟩
def site : CompilerConstantQueries.Site :=
  ⟨CopyPreconditions.Bodies.copyWrapper.loaded.identity.index, ⟨0,2⟩,
    #[.field "kind", .field "function", .field "constant"]⟩
def evidence : Array CompilerConstantEvidence :=
  (PreparedReflection.actual.compiler.constants.evidence.filter (·.site == site)).map (·.query)

theorem literal : constant.value = .Val .ZeroSized 206 := by with_unfolding_all rfl
theorem normalization : normalizationFromEvidence evidence CopyPreconditions.Bodies.copyWrapper.fnInstance
    (.Val .ZeroSized 206) = .ok (.Val .ZeroSized 206) := by with_unfolding_all rfl
theorem evaluation : evaluationFromEvidence evidence CopyPreconditions.Bodies.copyWrapper.fnInstance
    (.Val .ZeroSized 206) constant.span = .ok .ZeroSized := by with_unfolding_all rfl

def layoutQuery := PreparedReflection.actual.compiler.runtime.lookup 206
theorem layout_supported : layoutQuery.isOk = true := by decide +kernel
def functionLayout := checkedOk layoutQuery layout_supported
theorem layout_eq : layoutQuery = .ok functionLayout := checkedOk_eq _ _

open Lean Elab Tactic in
elab "simp_guard_function_constant" : tactic => do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith "Miri.Interpreter.constantType" then some (mkIdent name) else none
  let names := names.toArray
  evalTactic (← `(tactic| simp_all (config := {maxSteps := 1000000}) [
    CompilerConstantMachine.evalAtBound, ConstantMachine.fromCompiler,
    ConstantMachine.evalOperandWithLayout, evalConstOperandWithLayout,
    evalMirConstantWithLayout, constValueToOpWithLayout, valueToOpWithLayout,
    ConstantQueries.valueQueries, MachineHooks.currentFrame,
    Storage.withCurrent, Stack.currentFrame?, bind, EStateM.bind,
    get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure,
    Except.bind, Except.pure, site, evidence, constant, literal, $[$names:ident],*]))

theorem function_eval_at_bound
    (source : PreparedContracts.SourceComparator)
    (functions : FunctionPointers.Hooks MiriMemoryKind Machine.RootUser Unit)
    (arithmetic : PointerArithmetic)
    (externStatic : DefId → MachineHooks.M MiriMemoryKind Machine.RootUser (Pointer Provenance))
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (bodyIndex : frame.bodyIdentity.index = CopyPreconditions.Bodies.copyWrapper.loaded.identity.index)
    (location : frame.location = .mir ⟨0,2⟩)
    (fnInstance : frame.functionInstance = CopyPreconditions.Bodies.copyWrapper.fnInstance) :
    CompilerConstantMachine.evalAtBound PreparedReflection.actual.compiler.constantBinding site functions
      arithmetic externStatic MemoryErrors.constant constant none none
      (Storage.withCurrent frames frame machine) =
      .ok ⟨.immediate .uninit,functionLayout⟩ (Storage.withCurrent frames frame machine) := by
  have compatible := RootCompilerFacts.constant_binding_compatible source
  have norm := normalization
  have eval := evaluation
  unfold CompilerConstantMachine.evalAtBound
  simp only [constant]
  simp_guard_function_constant
  have layoutQueryIs : PreparedReflection.actual.compiler.runtime.lookup 206 = .ok functionLayout := layout_eq
  rw [layoutQueryIs]
  unfold_internal ".Interpreter.metadata"
  rfl

theorem function_operand [DecidableEq MiriMemoryKind]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (bodyIndex : frame.bodyIdentity.index = CopyPreconditions.Bodies.copyWrapper.loaded.identity.index)
    (location : frame.location = .mir ⟨0,2⟩)
    (fnInstance : frame.functionInstance = CopyPreconditions.Bodies.copyWrapper.fnInstance) :
    OperandMachine.evalOperandAt (ExecutionMachine.operandHooks
      (ExecutionMachine.withValidation (PreparedContracts.actualConfig options () remaining span) limits))
      () (OperandPath.instruction "function") (.Constant constant) none
      (Storage.withCurrent frames frame machine) =
      .ok ⟨.immediate .uninit,functionLayout⟩ (Storage.withCurrent frames frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let state := Storage.withCurrent frames frame machine
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨externStatic, constantAt⟩ := fields.constantAt debugOff
  have currentSite : CompilerOperandSites.current
      ((OperandPath.instruction "function").push (.field "constant")) state = .ok site state := by
    simp [CompilerOperandSites.current, MachineHooks.currentFrame, state, Storage.withCurrent,
      Stack.currentFrame?, site, bodyIndex, location, Bind.bind, EStateM.bind,
      get, getThe, MonadStateOf.get, EStateM.get, Pure.pure, EStateM.pure,
      OperandPath.instruction]
  have result := function_eval_at_bound source config.functions config.arithmetic externStatic
    frames frame machine bodyIndex location fnInstance
  change config.operands.constantAt ()
    ((OperandPath.instruction "function").push (.field "constant")) constant none state = _
  rw [constantAt]
  simpa [currentSite, state, config, OperandPath.rvalue, Bind.bind, EStateM.bind,
    Pure.pure, EStateM.pure] using result

#print axioms function_eval_at_bound
#print axioms function_operand
end
end DuplicatePrefix.GuardFunctionConstant

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.GuardFunctionConstant.function_eval_at_bound,
      ``DuplicatePrefix.GuardFunctionConstant.function_operand] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved guard function constant dependency {dependency}"
