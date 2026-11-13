import Miri.Input.WorldValTree
import Miri.Input.RuntimeArrayQueries
import Miri.Interpreter.ConstantMachine

/-! Source eval_mir_constant/const_val_to_op event cuts. Raw MIR constants are
evaluated in the execution's compiler World, then use the ordinary stateful
constant pointer adjustment and allocation conversion. -/
namespace Miri.Input.CompilerMirConstants
open Miri.ABI Miri.Interpreter Miri.Memory

def convert (runtime : RuntimeMetadata)
    (types : RuntimeArrayQueries.Access (MachineHooks.State K User))
    (functions : FunctionPointers.Hooks K User Other) (arithmetic : PointerArithmetic)
    (externStatic : Miri.MIR.DefId → MachineHooks.M K User (Pointer Provenance))
    (classifyError : ConstantError → StepError)
    (ty : Miri.MIR.TyId) (value : Miri.MIR.ConstValue) (known : Option LocalLayout)
    (checkKnown : Option (LocalLayout → LocalLayout → MachineHooks.M K User Bool)) :
    MachineHooks.M K User (OpTy Provenance) := do
  let layout ← match known with
    | none => RuntimeArrayQueries.layoutOf types ty
    | some expected => do
      if let some check := checkKnown then
        let actual ← RuntimeArrayQueries.layoutOf types ty
        unless ← check actual expected do
          throw (.invalidProgram "known constant layout differs from execution-world layout")
      pure expected
  ConstantMachine.evalValueWithLayout runtime functions arithmetic externStatic
    classifyError value ty (some layout) none


def hook (runtime : RuntimeMetadata)
    (types : RuntimeArrayQueries.Access (MachineHooks.State K User))
    (functions : FunctionPointers.Hooks K User Other) (arithmetic : PointerArithmetic)
    (externStatic : Miri.MIR.DefId → MachineHooks.M K User (Pointer Provenance))
    (classifyError : ConstantError → StepError)
    (constant : Miri.MIR.ConstOperand) (known : Option LocalLayout)
    (checkKnown : Option (LocalLayout → LocalLayout → MachineHooks.M K User Bool)) :
    MachineHooks.M K User (OpTy Provenance) := do
  let (ty,value) ← RuntimeArrayQueries.performCompiler types do
    RuntimeArrayTypes.liftType (WorldValTree.evaluate runtime constant.span constant.value)
  convert runtime types functions arithmetic externStatic classifyError ty value known checkKnown

end Miri.Input.CompilerMirConstants
