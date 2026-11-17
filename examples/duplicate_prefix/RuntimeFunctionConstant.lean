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

def constant : ConstOperand := ⟨⟨191⟩, none, .Val .ZeroSized 127⟩

theorem literal : constant.value = .Val .ZeroSized 127 := by with_unfolding_all rfl
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
    ConstantMachine.evalOperandWithLayout PreparedReflection.actual.compiler.runtime functions arithmetic externStatic MemoryErrors.constant constant none none
      (Storage.withCurrent framesBefore frame machine) =
      .ok ⟨.immediate .uninit, RuntimeCallQueries.functionLayout⟩
        (Storage.withCurrent framesBefore frame machine) := by
  unfold ConstantMachine.evalOperandWithLayout
  rw [literal]
  simp only [ConstantMachine.evalValueWithLayout, Option.map_none]
  unfold valueToOpWithLayout
  have layout : PreparedReflection.actual.compiler.runtime.lookup 127 = .ok RuntimeCallQueries.functionLayout := RuntimeCallQueries.functionLayout_query
  rw [layout]
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
    OperandMachine.evalOperand
      (ExecutionMachine.operandHooks (ExecutionMachine.withValidation
        (PreparedContracts.actualConfig options () remaining span) limits))
      ()  (.Constant constant) none
      (Storage.withCurrent framesBefore frame machine) =
      .ok ⟨.immediate .uninit, RuntimeCallQueries.functionLayout⟩
        (Storage.withCurrent framesBefore frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let state := Storage.withCurrent framesBefore frame machine
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨externStatic, constantAt⟩ := fields.constantAt debugOff
  change config.operands.constant () constant none state = _
  rw [constantAt]
  exact function_eval_at_bound source config.functions config.arithmetic externStatic
    framesBefore frame machine bodyIndex location fnInstance

end
end DuplicatePrefix.RuntimeFunctionConstant

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.RuntimeFunctionConstant.function_eval_at_bound,
      ``DuplicatePrefix.RuntimeFunctionConstant.function_operand] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved runtime function constant dependency {dependency}"
