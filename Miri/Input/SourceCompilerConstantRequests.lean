import Miri.Input.SourceCompilerConstants
import Miri.Interpreter.MachineHooks

/-! Resolve a deferred MIR constant only at an actual operand/required-constant
request. Compiler-evaluated witness values are input; no CTFE runs here. -/
namespace Miri.Input.SourceCompilerConstantRequests
open Miri.Interpreter

/-- Scalar/ZST values need no allocation-identity renaming. Other witness
representations remain unavailable until their provenance equivalence is known. -/
def resolve (world : SourceCompilerWorld.World) (constant : MIR.ConstOperand) :
    Except String (SourceCompilerWorld.World × MIR.ConstOperand) := do
  match constant.value with
  | .Val .. => return (world,constant)
  | .SourceRequest token expected =>
    let request ← SourceCompilerWorld.constantRequest world token
    unless request.expectedType == expected do throw "source constant token/type mismatch"
    let (world,actual,value) ← SourceCompilerConstants.demand world request
    unless actual == expected do throw "compiler-evaluated constant result/type mismatch"
    let value ← match value with
      | .scalar bits bytes => pure (MIR.ConstValue.Scalar (.Int bits bytes))
      | .zeroSized => pure MIR.ConstValue.ZeroSized
      | _ => throw "compiler-evaluated allocation constant identity/provenance unavailable"
    return (world,{constant with value := .Val value actual})

/-- Concrete operands preserve the original action/state exactly: they neither
read nor write the source World. Deferred requests use the one shared lens. -/
def consume (access : SourceCompilerWorld.Access (MachineHooks.State K U))
    (constant : MIR.ConstOperand) : MachineHooks.M K U MIR.ConstOperand := do
  match constant.value with
  | .Val .. => return constant
  | .SourceRequest .. =>
    let some world := access.get (← get)
      | throw (.unsupported "source constant request requires the shared compiler World")
    let (world,resolved) ← match resolve world constant with
      | .ok value => pure value
      | .error message => throw (.unsupported s!"compiler constant: {message}")
    modify fun state => access.put state world
    return resolved
end Miri.Input.SourceCompilerConstantRequests
