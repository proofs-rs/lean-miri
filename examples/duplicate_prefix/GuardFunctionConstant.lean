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

def constant : ConstOperand := ⟨⟨119⟩, none, .Val .ZeroSized 101⟩
theorem literal : constant.value = .Val .ZeroSized 101 := by with_unfolding_all rfl
def layoutQuery := PreparedReflection.actual.compiler.runtime.lookup 101
theorem layout_supported : layoutQuery.isOk = true := by decide +kernel
def functionLayout := checkedOk (PreparedReflection.actual.layoutResults[101]'(by decide +kernel)) (by decide +kernel)
theorem layout_eq : layoutQuery = .ok functionLayout := by decide +kernel

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
    ConstantMachine.evalOperandWithLayout PreparedReflection.actual.compiler.runtime functions
      arithmetic externStatic MemoryErrors.constant constant none none
      (Storage.withCurrent frames frame machine) =
      .ok ⟨.immediate .uninit,functionLayout⟩ (Storage.withCurrent frames frame machine) := by
  unfold ConstantMachine.evalOperandWithLayout
  rw [literal]
  simp only [ConstantMachine.evalValueWithLayout, Option.map_none]
  unfold valueToOpWithLayout
  have layout : PreparedReflection.actual.compiler.runtime.lookup 101 = .ok functionLayout := layout_eq
  rw [layout]
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
    OperandMachine.evalOperand (ExecutionMachine.operandHooks
      (ExecutionMachine.withValidation (PreparedContracts.actualConfig options () remaining span) limits))
      ()  (.Constant constant) none
      (Storage.withCurrent frames frame machine) =
      .ok ⟨.immediate .uninit,functionLayout⟩ (Storage.withCurrent frames frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let state := Storage.withCurrent frames frame machine
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨externStatic, constantAt⟩ := fields.constantAt debugOff
  change config.operands.constant () constant none state = _
  rw [constantAt]
  exact function_eval_at_bound source config.functions config.arithmetic externStatic
    frames frame machine bodyIndex location fnInstance

end
end DuplicatePrefix.GuardFunctionConstant

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.GuardFunctionConstant.function_eval_at_bound,
      ``DuplicatePrefix.GuardFunctionConstant.function_operand] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved guard function constant dependency {dependency}"
