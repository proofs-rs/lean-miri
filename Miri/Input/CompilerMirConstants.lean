import Miri.Input.RuntimeArrayQueries
import Miri.Interpreter.ConstantMachine

/-! Executable MIR carries rustc evaluated constants. Keep the ordinary
constant pointer adjustment and allocation conversion in the execution World.
Unevaluated and type-system constants have no runtime fallback. -/
namespace Miri.Input.CompilerMirConstants
open Miri.ABI Miri.Interpreter Miri.Memory

/-- A concrete executable operand must arrive with rustc's evaluated value. -/
def requireEvaluated (constant : Miri.MIR.ConstOperand) : Except String (Miri.MIR.TyId × Miri.MIR.ConstValue) :=
  match constant.value with
  | .Val value ty => pure (ty,value)
  | .Ty .. | .Unevaluated .. =>
    throw "executable MIR constant lacks a rustc evaluated value"

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
  let (ty,value) ← match requireEvaluated constant with
    | .ok answer => pure answer
    | .error reason => throw (.unsupported reason)
  convert runtime types functions arithmetic externStatic classifyError ty value known checkKnown

end Miri.Input.CompilerMirConstants
