import Miri.Interpreter.ConstantMachine
import empty_function.LocalUnit
namespace EmptyFunction.Literal
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
set_option autoImplicit false
variable {K U Other : Type}
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
 theorem eval_unit (runtime : RuntimeMetadata)
    (functions : FunctionPointers.Hooks K U Other) (arithmetic : PointerArithmetic)
    (external : DefId → MachineHooks.M K U (Pointer Provenance))
    (classify : ConstantError → StepError) (literal : ConstOperand) (unit : LocalLayout)
    (frame : LocalUnit.F) (frames : Array LocalUnit.F) (machine : MachineHooks.MachineState K U)
    (value : literal.value = .Val .ZeroSized unit.ty) :
    ConstantMachine.evalOperandWithLayout runtime functions arithmetic external classify literal
      (some unit) none (LocalUnit.current frames frame machine) =
      .ok ⟨.immediate .uninit, unit⟩ (LocalUnit.current frames frame machine) := by
  simp only [ConstantMachine.evalOperandWithLayout, value]
  simp [ConstantMachine.evalValueWithLayout, LocalUnit.current, Stack.currentFrame?,
    valueToOpWithLayout, constValueToOp,
    get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure]
end EmptyFunction.Literal
