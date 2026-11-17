import duplicate_prefix.AddFunctionFacts
import duplicate_prefix.CopyHelperUnit
import duplicate_prefix.CopyLanguageGuard
import duplicate_prefix.HelperCompilerFacts
import duplicate_prefix.ActualLocalCopy
namespace DuplicatePrefix.AddFunctionConstant
noncomputable section
open Miri Miri.ABI Miri.Input Miri.MIR Miri.Interpreter Miri.Memory Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

noncomputable def constant : ConstOperand := match HelperCompilerFacts.addCall.function with
  | .Constant constant => constant
  | _ => ⟨⟨0⟩,none,.Val .ZeroSized 30⟩
theorem literal : constant.value = .Val .ZeroSized 30 := by with_unfolding_all rfl
theorem function_eval_at_bound
    (source : PreparedContracts.SourceComparator)
    (functions : FunctionPointers.Hooks MiriMemoryKind Machine.RootUser Unit)
    (arithmetic : PointerArithmetic)
    (externStatic : DefId → MachineHooks.M MiriMemoryKind Machine.RootUser (Pointer Provenance))
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (bodyIndex : frame.bodyIdentity.index = RootBody.reflected.body.identity.index)
    (location : frame.location = .mir ⟨7,13⟩)
    (fnInstance : frame.functionInstance = RootBody.reflected.functionInstance) :
    ConstantMachine.evalOperandWithLayout PreparedReflection.actual.compiler.runtime functions arithmetic externStatic MemoryErrors.constant
      constant none none
      (Storage.withCurrent framesBefore frame machine) =
    .ok ⟨.immediate .uninit,AddFunctionFacts.functionLayout⟩
      (Storage.withCurrent framesBefore frame machine) := by
  unfold ConstantMachine.evalOperandWithLayout
  rw [literal]
  simp only [ConstantMachine.evalValueWithLayout, Option.map_none]
  unfold valueToOpWithLayout
  have layout : PreparedReflection.actual.compiler.runtime.lookup 30 = .ok AddFunctionFacts.functionLayout := AddFunctionFacts.functionLayout_query
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
    (bodyIndex : frame.bodyIdentity.index = RootBody.reflected.body.identity.index)
    (location : frame.location = .mir ⟨7,13⟩)
    (fnInstance : frame.functionInstance = RootBody.reflected.functionInstance) :
    OperandMachine.evalOperand
      (ExecutionMachine.operandHooks (ExecutionMachine.withValidation
        (PreparedContracts.actualConfig options () remaining span) limits))
      () (.Constant constant)
      none (Storage.withCurrent framesBefore frame machine) =
    .ok ⟨.immediate .uninit,AddFunctionFacts.functionLayout⟩
      (Storage.withCurrent framesBefore frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let state := Storage.withCurrent framesBefore frame machine
  obtain ⟨externStatic, constantAt⟩ := (CanonicalConfigFacts.actual_fields options () remaining span).constantAt debugOff
  change config.operands.constant () constant none state = _
  rw [constantAt]
  exact function_eval_at_bound source config.functions config.arithmetic externStatic
    framesBefore frame machine bodyIndex location fnInstance

end
end DuplicatePrefix.AddFunctionConstant

open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.AddFunctionConstant.function_eval_at_bound, ``DuplicatePrefix.AddFunctionConstant.function_operand] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved source metadata call dependency {dependency}"
