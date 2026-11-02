import duplicate_prefix.LocalOperands
import Miri.Interpreter.OperandMachine

/-! Source-dispatch composition for whole-local operands with no projection. -/

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace DuplicatePrefix.OperandDispatch
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

def wholeLocal (id : LocalId) : Place := ⟨id, #[]⟩

/-- The real place evaluator runs the local read, an empty projection loop, and
the supplied actual `checkPlaceType` effect in source order. -/
theorem evalPlaceToOp_wholeLocal
    (hooks : OperandMachine.Hooks K User Choice) (choice : Choice)
    (localId : LocalId) (known : Option LocalLayout)
    (before after : MachineHooks.State K User) (op : OpTy Provenance)
    (localRead : OperandMachine.localToOp hooks choice localId known before = .ok op after)
    (typeCheck : hooks.checkPlaceType choice (wholeLocal localId) op after = .ok () after) :
    OperandMachine.evalPlaceToOp hooks choice (wholeLocal localId) known before = .ok op after := by
  simp [OperandMachine.evalPlaceToOp, wholeLocal, Bind.bind, EStateM.instMonad,
    EStateM.bind, localRead, EStateM.pure, pure, Array.forIn_toList]
  simp only [wholeLocal] at typeCheck
  rw [typeCheck]

theorem evalOperand_copy_wholeLocal
    (hooks : OperandMachine.Hooks K User Choice) (choice : Choice)
    (localId : LocalId) (known : Option LocalLayout)
    (before after : MachineHooks.State K User) (op : OpTy Provenance)
    (localRead : OperandMachine.localToOp hooks choice localId known before = .ok op after)
    (typeCheck : hooks.checkPlaceType choice (wholeLocal localId) op after = .ok () after) :
    OperandMachine.evalOperand hooks choice (.Copy (wholeLocal localId)) known before =
      .ok op after := by
  exact evalPlaceToOp_wholeLocal hooks choice localId known before after op localRead typeCheck

theorem evalOperand_move_wholeLocal
    (hooks : OperandMachine.Hooks K User Choice) (choice : Choice)
    (localId : LocalId) (known : Option LocalLayout)
    (before after : MachineHooks.State K User) (op : OpTy Provenance)
    (localRead : OperandMachine.localToOp hooks choice localId known before = .ok op after)
    (typeCheck : hooks.checkPlaceType choice (wholeLocal localId) op after = .ok () after) :
    OperandMachine.evalOperand hooks choice (.Move (wholeLocal localId)) known before =
      .ok op after := by
  exact evalPlaceToOp_wholeLocal hooks choice localId known before after op localRead typeCheck

theorem evalOperandAt_copy_wholeLocal
    (hooks : OperandMachine.Hooks K User Choice) (choice : Choice)
    (path : OperandPath) (localId : LocalId) (known : Option LocalLayout)
    (before after : MachineHooks.State K User) (op : OpTy Provenance)
    (localRead : OperandMachine.localToOp hooks choice localId known before = .ok op after)
    (typeCheck : hooks.checkPlaceType choice (wholeLocal localId) op after = .ok () after) :
    OperandMachine.evalOperandAt hooks choice path (.Copy (wholeLocal localId)) known before =
      .ok op after := by
  exact evalOperand_copy_wholeLocal hooks choice localId known before after op localRead typeCheck

theorem evalOperandAt_move_wholeLocal
    (hooks : OperandMachine.Hooks K User Choice) (choice : Choice)
    (path : OperandPath) (localId : LocalId) (known : Option LocalLayout)
    (before after : MachineHooks.State K User) (op : OpTy Provenance)
    (localRead : OperandMachine.localToOp hooks choice localId known before = .ok op after)
    (typeCheck : hooks.checkPlaceType choice (wholeLocal localId) op after = .ok () after) :
    OperandMachine.evalOperandAt hooks choice path (.Move (wholeLocal localId)) known before =
      .ok op after := by
  exact evalOperand_move_wholeLocal hooks choice localId known before after op localRead typeCheck

#print axioms evalPlaceToOp_wholeLocal
#print axioms evalOperand_copy_wholeLocal
#print axioms evalOperand_move_wholeLocal
#print axioms evalOperandAt_copy_wholeLocal
#print axioms evalOperandAt_move_wholeLocal

end DuplicatePrefix.OperandDispatch
