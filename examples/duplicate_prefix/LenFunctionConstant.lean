import duplicate_prefix.LenCallQueries
import duplicate_prefix.CopyHelperUnit
import duplicate_prefix.CopyLanguageGuard
import duplicate_prefix.HelperCompilerFacts
import duplicate_prefix.ActualLocalCopy
namespace DuplicatePrefix.LenFunctionConstant
noncomputable section
open Miri Miri.ABI Miri.Input Miri.MIR Miri.Interpreter Miri.Memory Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

noncomputable def constant : ConstOperand := match LenHelper.resolved.function with
  | .Constant constant => constant
  | _ => ⟨⟨0⟩,none,.Val .ZeroSized 10⟩
noncomputable def site : CompilerConstantQueries.Site := ⟨RootBody.reflected.body.identity.index, ⟨2,12⟩,
  #[.field "kind",.field "function",.field "constant"]⟩
theorem literal : constant.value = .Val .ZeroSized 10 := by with_unfolding_all rfl
theorem normalization : normalizationFromEvidence
    ((PreparedReflection.actual.compiler.constants.evidence.filter (·.site == site)).map (·.query))
    RootBody.reflected.functionInstance (.Val .ZeroSized 10) = .ok (.Val .ZeroSized 10) := by with_unfolding_all rfl

open Lean Elab Tactic in
elab "simp_function_constant" : tactic => do
  let found := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith "Miri.Interpreter.constantType" then some (mkIdent name) else none
  let names := found.toArray
  evalTactic (← `(tactic| simp_all (config := {maxSteps := 1000000}) [
    CompilerConstantMachine.evalAtBound, ConstantMachine.fromCompiler,
    ConstantMachine.evalOperandWithLayout, evalConstOperandWithLayout,
    evalMirConstantWithLayout, constValueToOpWithLayout, valueToOpWithLayout,
    ConstantQueries.valueQueries, MachineHooks.currentFrame,
    Storage.withCurrent, Stack.currentFrame?, bind, EStateM.bind,
    get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure,
    Except.bind, Except.pure, site, literal, $[$names:ident],*]))

theorem function_eval_at_bound
    (source : PreparedContracts.SourceComparator)
    (functions : FunctionPointers.Hooks MiriMemoryKind Machine.RootUser Unit)
    (arithmetic : PointerArithmetic)
    (externStatic : DefId → MachineHooks.M MiriMemoryKind Machine.RootUser (Pointer Provenance))
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (bodyIndex : frame.bodyIdentity.index = RootBody.reflected.body.identity.index)
    (location : frame.location = .mir ⟨2,12⟩)
    (fnInstance : frame.functionInstance = RootBody.reflected.functionInstance) :
    CompilerConstantMachine.evalAtBound PreparedReflection.actual.compiler.constantBinding
      site functions arithmetic externStatic MemoryErrors.constant
      constant none none
      (Storage.withCurrent framesBefore frame machine) =
    .ok ⟨.immediate .uninit,LenCallQueries.functionLayout⟩
      (Storage.withCurrent framesBefore frame machine) := by
  have compatible := RootCompilerFacts.constant_binding_compatible source
  have norm : normalizationFromEvidence
      ((PreparedReflection.actual.compiler.constants.evidence.filter (·.site == site)).map (·.query))
      RootBody.reflected.functionInstance constant.value =
      .ok constant.value := by
    rw [literal]
    exact normalization
  have layout := LenCallQueries.functionLayout_query
  have shape := LenCallQueries.functionLayout_shape
  simp_function_constant
  have compilerLayout : PreparedReflection.actual.compiler.runtime.lookup 10 = .ok LenCallQueries.functionLayout := by
    change PreparedReflection.actual.runtime.lookup 10 = _
    exact layout
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
    (bodyIndex : frame.bodyIdentity.index = RootBody.reflected.body.identity.index)
    (location : frame.location = .mir ⟨2,12⟩)
    (fnInstance : frame.functionInstance = RootBody.reflected.functionInstance) :
    OperandMachine.evalOperandAt
      (ExecutionMachine.operandHooks (ExecutionMachine.withValidation
        (PreparedContracts.actualConfig options () remaining span) limits))
      () (OperandPath.instruction "function") (.Constant constant)
      none (Storage.withCurrent framesBefore frame machine) =
    .ok ⟨.immediate .uninit,LenCallQueries.functionLayout⟩
      (Storage.withCurrent framesBefore frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let state := Storage.withCurrent framesBefore frame machine
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨externStatic, constantAt⟩ := fields.constantAt debugOff
  have currentSite : CompilerOperandSites.current
      ((OperandPath.instruction "function").push (.field "constant")) state = .ok site state := by
    simp [CompilerOperandSites.current, MachineHooks.currentFrame,
      state, Storage.withCurrent, Stack.currentFrame?, site, bodyIndex, location,
      Bind.bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, Pure.pure, EStateM.pure,
      OperandPath.instruction]
  have siteLit : CompilerOperandSites.current
      ((OperandPath.instruction "function").push (.field "constant"))
      (Storage.withCurrent framesBefore frame machine) =
      .ok site (Storage.withCurrent framesBefore frame machine) := by
    simpa [OperandPath.rvalue, state] using currentSite
  have result := function_eval_at_bound source config.functions config.arithmetic externStatic
    framesBefore frame machine bodyIndex location fnInstance
  change config.operands.constantAt ()
    ((OperandPath.instruction "function").push (.field "constant")) constant
    none state = _
  rw [constantAt]
  simpa [siteLit, state, config, OperandPath.rvalue, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure] using result

end
end DuplicatePrefix.LenFunctionConstant

open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.LenFunctionConstant.function_eval_at_bound, ``DuplicatePrefix.LenFunctionConstant.function_operand] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved source metadata call dependency {dependency}"
