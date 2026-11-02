import duplicate_prefix.BoolSwitch
namespace DuplicatePrefix.BoolAssert
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem of_read {P Layout Extra Machine Choice Op Imm : Type}
    (hooks : TerminatorHooks P Layout Extra Machine Choice Op Imm) (choice : Choice)
    (terminator : Terminator) (condition : Miri.MIR.Operand)
    (expected : Bool) (message : AssertKind) (target : BasicBlockId) (unwind : UnwindAction)
    (before evaluated : StepState P Layout Extra Machine)
    (kind : terminator.kind = .Assert condition expected message target unwind)
    (read : hooks.readAssertCondition choice condition before = (evaluated,.ok expected)) :
    ControlFlow.evalTerminator hooks choice terminator before = ControlFlow.goToBlock target evaluated := by
  unfold ControlFlow.evalTerminator
  rw [kind]
  simp only [read,beq_self_eq_true,Bool.or_true,ite_true]
  rfl

theorem dispatch [DecidableEq K]
    (config : ExecutionMachine.Config K User Choice Other Extern Host)
    (limits : ExecutionMachine.Limits) (choice : Choice)
    (terminator : Terminator) (condition : Miri.MIR.Operand)
    (expected : Bool) (message : AssertKind) (target : BasicBlockId) (unwind : UnwindAction)
    (before evaluated : MachineHooks.State K User) (layout : LocalLayout)
    (kind : terminator.kind = .Assert condition expected message target unwind)
    (read : (do
      PlaceMachine.readImmediate (ExecutionMachine.withValidation config limits).access
        (← OperandMachine.evalOperandAt
          (ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits)) choice
          (OperandPath.instruction "condition") condition none)) before =
      .ok (ScalarOperations.boolImmediate expected layout) evaluated) :
    (ExecutionMachine.stepHooks config limits).terminator choice terminator before =
      ControlFlow.goToBlock target evaluated := by
  change ControlFlow.evalTerminator _ choice terminator before = _
  apply of_read _ choice terminator condition expected message target unwind before evaluated kind
  simp_switch_comparison

#print axioms dispatch
end DuplicatePrefix.BoolAssert
