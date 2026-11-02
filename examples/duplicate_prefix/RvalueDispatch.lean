import duplicate_prefix.ScalarOperations
import duplicate_prefix.LocalWrites
import duplicate_prefix.OperandDispatch
import Miri.Interpreter.Rvalue
import Miri.Interpreter.ExecutionMachine

/-! Exact successful staging equations for the real `Rvalue` dispatcher.
Machine operations remain the existing interpreter hooks and are stated as
their exact EStateM transitions; this module adds no arithmetic semantics. -/

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace DuplicatePrefix.RvalueDispatch
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows.RetagPolicy

open Lean Elab Tactic in
elab "simp_rvalue_assert" : tactic => do
  let found := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith ".Interpreter.assertRvalueLayout" then some (mkIdent name) else none
  match found with
  | [name] => evalTactic (← `(tactic| simp_all [$name:ident]))
  | _ => throwError "expected the unique source assertRvalueLayout helper"

theorem binaryOp
    (hooks : RvalueHooks Provenance (MachineHooks.State K User) Choice (RuntimePlace Provenance))
    (choice : Choice) (operator : BinOp) (left right : Operand)
    (dest : Place) (destValue : RuntimePlace Provenance)
    (leftOp rightOp : OpTy Provenance)
    (leftImm rightImm result : RvalueImmTy Provenance)
    (s0 s1 s2 s3 s4 s5 s6 s7 : MachineHooks.State K User)
    (evalDest : hooks.evalPlace choice dest true s0 = .ok destValue s1)
    (evalLeft : hooks.evalOperandAt choice (OperandPath.rvalue "left") left
      (if operator.leftHomogeneous then some (hooks.placeLayout destValue) else none) s1 = .ok leftOp s2)
    (readLeft : hooks.readImmediate choice leftOp s2 = .ok leftImm s3)
    (evalRight : hooks.evalOperandAt choice (OperandPath.rvalue "right") right
      (if operator.rightHomogeneous then some leftImm.layout else none) s3 = .ok rightOp s4)
    (readRight : hooks.readImmediate choice rightOp s4 = .ok rightImm s5)
    (binary : hooks.binaryOp choice operator leftImm rightImm s5 = .ok result s6)
    (resultLayout : result.layout = hooks.placeLayout destValue)
    (write : hooks.writeImmediate choice result.imm destValue s6 = .ok () s7) :
    evalRvalueIntoPlace hooks choice (.BinaryOp operator left right) dest s0 = .ok () s7 := by
  simp_all [evalRvalueIntoPlace, Bind.bind, EStateM.bind, OperandPath.rvalue]
  simp_rvalue_assert
  change EStateM.bind (EStateM.pure ())
    (fun _ => hooks.writeImmediate choice result.imm destValue) s6 = .ok () s7
  simp [EStateM.bind, EStateM.pure, write]

/-- The complete BinaryOp dispatcher reduces to its actual final write hook
once destination, operands, reads, scalar operation, and result layout have
been derived. This theorem does not assume that the write succeeds. -/
theorem binaryOp_to_write
    (hooks : RvalueHooks Provenance (MachineHooks.State K User) Choice (RuntimePlace Provenance))
    (choice : Choice) (operator : BinOp) (left right : Operand)
    (dest : Place) (destValue : RuntimePlace Provenance)
    (leftOp rightOp : OpTy Provenance)
    (leftImm rightImm result : RvalueImmTy Provenance)
    (s0 s1 s2 s3 s4 s5 s6 : MachineHooks.State K User)
    (evalDest : hooks.evalPlace choice dest true s0 = .ok destValue s1)
    (evalLeft : hooks.evalOperandAt choice (OperandPath.rvalue "left") left
      (if operator.leftHomogeneous then some (hooks.placeLayout destValue) else none) s1 = .ok leftOp s2)
    (readLeft : hooks.readImmediate choice leftOp s2 = .ok leftImm s3)
    (evalRight : hooks.evalOperandAt choice (OperandPath.rvalue "right") right
      (if operator.rightHomogeneous then some leftImm.layout else none) s3 = .ok rightOp s4)
    (readRight : hooks.readImmediate choice rightOp s4 = .ok rightImm s5)
    (binary : hooks.binaryOp choice operator leftImm rightImm s5 = .ok result s6)
    (resultLayout : result.layout = hooks.placeLayout destValue) :
    evalRvalueIntoPlace hooks choice (.BinaryOp operator left right) dest s0 =
      hooks.writeImmediate choice result.imm destValue s6 := by
  simp_all [evalRvalueIntoPlace, Bind.bind, EStateM.bind, OperandPath.rvalue]
  simp_rvalue_assert
  change EStateM.bind (EStateM.pure ())
    (fun _ => hooks.writeImmediate choice result.imm destValue) s6 =
    hooks.writeImmediate choice result.imm destValue s6
  simp [EStateM.bind, EStateM.pure]

/-- The source `.Use` branch evaluates its operand with its structural path and
destination layout, then executes the real retag-scoped copy effect. -/
theorem use_operand
    (hooks : RvalueHooks Provenance (MachineHooks.State K User) Choice (RuntimePlace Provenance))
    (choice : Choice) (operand : Operand) (retag : WithRetag) (dest : Place)
    (destValue : RuntimePlace Provenance) (op : OpTy Provenance)
    (s0 s1 s2 s3 : MachineHooks.State K User)
    (evalDest : hooks.evalPlace choice dest true s0 = .ok destValue s1)
    (evalSource : hooks.evalOperandAt choice (OperandPath.rvalue "operand") operand
      (some (hooks.placeLayout destValue)) s1 = .ok op s2)
    (copy : hooks.withRetagMode choice
      (if retag == .Yes then RetagMode.Default else RetagMode.None)
      (hooks.copyOp choice op destValue) s2 = .ok () s3) :
    evalRvalueIntoPlace hooks choice (.Use operand retag) dest s0 = .ok () s3 := by
  simp_all [evalRvalueIntoPlace, Bind.bind, EStateM.bind, OperandPath.rvalue]

/-- The canonical assembled machine's Eq stage delegates to the real scalar
operation provider. Only immutable type/layout query outcomes are premises;
the scalar comparison result is derived from `ScalarOperations.usize_eq`. -/
theorem canonical_usize_eq_binary_stage [DecidableEq K]
    (config : ExecutionMachine.Config K User Unit Other Extern Host)
    (limits : ExecutionMachine.Limits) (layout boolLayout : LocalLayout)
    (left right : UInt64) (state : MachineHooks.State K User)
    (classification : (ExecutionMachine.scalarHooks
      (ExecutionMachine.withValidation config limits)).classify () layout.ty = pure (.integer .usize))
    (boolQuery : (ExecutionMachine.scalarHooks
      (ExecutionMachine.withValidation config limits)).boolLayout () = pure boolLayout)
    (width : layout.layout.size = Size.ofBytes 8) :
    (ExecutionMachine.rvalueHooks config limits).binaryOp () .Eq
      (ScalarOperations.usizeImmediate left layout)
      (ScalarOperations.usizeImmediate right layout) state =
      .ok ⟨.scalar (.fromBool (left == right)), boolLayout⟩ state := by
  have scalar := ScalarOperations.usize_eq
    (ExecutionMachine.scalarHooks (ExecutionMachine.withValidation config limits))
    () layout boolLayout left right classification boolQuery width
  change ScalarOps.binary
    (ExecutionMachine.scalarHooks (ExecutionMachine.withValidation config limits))
    () .Eq (ScalarOperations.usizeImmediate left layout)
      (ScalarOperations.usizeImmediate right layout) state =
    (pure (⟨.scalar (.fromBool (left == right)), boolLayout⟩ : RvalueImmTy Provenance) :
      RvalueM (MachineHooks.State K User) (RvalueImmTy Provenance)) state
  exact congrFun scalar state

#print axioms binaryOp
#print axioms binaryOp_to_write
#print axioms use_operand
#print axioms canonical_usize_eq_binary_stage

end DuplicatePrefix.RvalueDispatch
