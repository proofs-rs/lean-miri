import duplicate_prefix.MetadataCallQueries
import duplicate_prefix.CopyHelperUnit
import duplicate_prefix.CopyLanguageGuard
import duplicate_prefix.HelperCompilerFacts
import duplicate_prefix.ActualLocalCopy
namespace DuplicatePrefix.MetadataFunctionConstant
noncomputable section
open Miri Miri.ABI Miri.Input Miri.MIR Miri.Interpreter Miri.Memory Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

noncomputable def constant : ConstOperand := match PtrMetadataHelper.resolved.function with
  | .Constant constant => constant
  | _ => ⟨⟨0⟩,none,.Val .ZeroSized 50⟩
theorem literal : constant.value = .Val .ZeroSized 50 := by with_unfolding_all rfl
theorem function_eval_at_bound
    (source : PreparedContracts.SourceComparator)
    (functions : FunctionPointers.Hooks MiriMemoryKind Machine.RootUser Unit)
    (arithmetic : PointerArithmetic)
    (externStatic : DefId → MachineHooks.M MiriMemoryKind Machine.RootUser (Pointer Provenance))
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (bodyIndex : frame.bodyIdentity.index = HelperCompilerFacts.lenBody.identity.index)
    (location : frame.location = .mir ⟨0,2⟩)
    (fnInstance : frame.functionInstance = HelperCompilerFacts.lenCall.callee) :
    ConstantMachine.evalOperandWithLayout PreparedReflection.actual.compiler.runtime functions arithmetic externStatic MemoryErrors.constant
      constant none none
      (Storage.withCurrent framesBefore frame machine) =
    .ok ⟨.immediate .uninit,MetadataCallQueries.functionLayout⟩
      (Storage.withCurrent framesBefore frame machine) := by
  unfold ConstantMachine.evalOperandWithLayout
  rw [literal]
  simp only [ConstantMachine.evalValueWithLayout, Option.map_none]
  unfold valueToOpWithLayout
  have layout : PreparedReflection.actual.compiler.runtime.lookup 50 = .ok MetadataCallQueries.functionLayout := MetadataCallQueries.functionLayout_query
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
    (bodyIndex : frame.bodyIdentity.index = HelperCompilerFacts.lenBody.identity.index)
    (location : frame.location = .mir ⟨0,2⟩)
    (fnInstance : frame.functionInstance = HelperCompilerFacts.lenCall.callee) :
    OperandMachine.evalOperand
      (ExecutionMachine.operandHooks (ExecutionMachine.withValidation
        (PreparedContracts.actualConfig options () remaining span) limits))
      () (.Constant constant)
      none (Storage.withCurrent framesBefore frame machine) =
    .ok ⟨.immediate .uninit,MetadataCallQueries.functionLayout⟩
      (Storage.withCurrent framesBefore frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let state := Storage.withCurrent framesBefore frame machine
  obtain ⟨externStatic, constantAt⟩ := (CanonicalConfigFacts.actual_fields options () remaining span).constantAt debugOff
  change config.operands.constant () constant none state = _
  rw [constantAt]
  exact function_eval_at_bound source config.functions config.arithmetic externStatic
    framesBefore frame machine bodyIndex location fnInstance

end
end DuplicatePrefix.MetadataFunctionConstant

open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.MetadataFunctionConstant.function_eval_at_bound, ``DuplicatePrefix.MetadataFunctionConstant.function_operand] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved source metadata call dependency {dependency}"
