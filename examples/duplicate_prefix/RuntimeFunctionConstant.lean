import duplicate_prefix.RuntimeCallQueries
import duplicate_prefix.RootCompilerFacts

/-! The actual zero-sized function operand at checkLanguage's terminator. -/
namespace DuplicatePrefix.RuntimeFunctionConstant
noncomputable section
open Miri Miri.ABI Miri.Input Miri.MIR Miri.Interpreter Miri.Memory
open DuplicatePrefix
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def constant : ConstOperand := ⟨⟨158⟩, none, .Val .ZeroSized 243⟩

def site : CompilerConstantQueries.Site :=
  ⟨CopyPreconditions.Bodies.checkLanguage.loaded.identity.index, ⟨0,3⟩,
    #[.field "kind", .field "function", .field "constant"]⟩
def evidence : Array CompilerConstantEvidence :=
  (PreparedReflection.actual.compiler.constants.evidence.filter (·.site == site)).map (·.query)

theorem literal : constant.value = .Val .ZeroSized 243 := by with_unfolding_all rfl
theorem normalization : normalizationFromEvidence evidence
    CopyPreconditions.Bodies.checkLanguage.fnInstance (.Val .ZeroSized 243) =
      .ok (.Val .ZeroSized 243) := by with_unfolding_all rfl
theorem evaluation : evaluationFromEvidence evidence
    CopyPreconditions.Bodies.checkLanguage.fnInstance (.Val .ZeroSized 243) constant.span =
      .ok .ZeroSized := by with_unfolding_all rfl

open Lean Elab Tactic in
elab "simp_runtime_function_constant" : tactic => do
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
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (bodyIndex : frame.bodyIdentity.index = CopyPreconditions.Bodies.checkLanguage.loaded.identity.index)
    (location : frame.location = .mir ⟨0,3⟩)
    (fnInstance : frame.functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance) :
    CompilerConstantMachine.evalAtBound PreparedReflection.actual.compiler.constantBinding
      site functions arithmetic externStatic MemoryErrors.constant constant none none
      (Storage.withCurrent framesBefore frame machine) =
      .ok ⟨.immediate .uninit, RuntimeCallQueries.functionLayout⟩
        (Storage.withCurrent framesBefore frame machine) := by
  have compatible := RootCompilerFacts.constant_binding_compatible source
  have norm : normalizationFromEvidence evidence CopyPreconditions.Bodies.checkLanguage.fnInstance
      (.Val .ZeroSized 243) = .ok (.Val .ZeroSized 243) := normalization
  have eval : evaluationFromEvidence evidence CopyPreconditions.Bodies.checkLanguage.fnInstance
      (.Val .ZeroSized 243) constant.span = .ok .ZeroSized := evaluation
  unfold CompilerConstantMachine.evalAtBound
  simp only [constant]
  simp_runtime_function_constant
  have compilerLayout : PreparedReflection.actual.compiler.runtime.lookup 243 =
      .ok RuntimeCallQueries.functionLayout := by
    change PreparedReflection.actual.runtime.lookup 243 = _
    exact RuntimeCallQueries.functionLayout_query
  rw [compilerLayout]
  unfold_internal ".Interpreter.metadata"
  rfl

theorem function_operand
    [DecidableEq MiriMemoryKind]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (bodyIndex : frame.bodyIdentity.index = CopyPreconditions.Bodies.checkLanguage.loaded.identity.index)
    (location : frame.location = .mir ⟨0,3⟩)
    (fnInstance : frame.functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance) :
    OperandMachine.evalOperandAt
      (ExecutionMachine.operandHooks (ExecutionMachine.withValidation
        (PreparedContracts.actualConfig options () remaining span) limits))
      () (OperandPath.instruction "function") (.Constant constant) none
      (Storage.withCurrent framesBefore frame machine) =
      .ok ⟨.immediate .uninit, RuntimeCallQueries.functionLayout⟩
        (Storage.withCurrent framesBefore frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let state := Storage.withCurrent framesBefore frame machine
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨externStatic, constantAt⟩ := fields.constantAt debugOff
  have currentSite : CompilerOperandSites.current
      ((OperandPath.instruction "function").push (.field "constant")) state = .ok site state := by
    simp [CompilerOperandSites.current, MachineHooks.currentFrame,
      state, Storage.withCurrent, Stack.currentFrame?, site, bodyIndex, location,
      Bind.bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
      Pure.pure, EStateM.pure, OperandPath.instruction]
  have siteLit : CompilerOperandSites.current
      ((OperandPath.instruction "function").push (.field "constant"))
      (Storage.withCurrent framesBefore frame machine) =
      .ok site (Storage.withCurrent framesBefore frame machine) := by
    simpa [OperandPath.rvalue, state] using currentSite
  have result := function_eval_at_bound source config.functions config.arithmetic externStatic
    framesBefore frame machine bodyIndex location fnInstance
  change config.operands.constantAt ()
    ((OperandPath.instruction "function").push (.field "constant")) constant none state = _
  rw [constantAt]
  simpa [siteLit, state, config, OperandPath.rvalue, Bind.bind,
    EStateM.bind, Pure.pure, EStateM.pure] using result

end
end DuplicatePrefix.RuntimeFunctionConstant

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.RuntimeFunctionConstant.function_eval_at_bound,
      ``DuplicatePrefix.RuntimeFunctionConstant.function_operand] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved runtime function constant dependency {dependency}"
