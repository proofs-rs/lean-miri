import Miri.Input.CompilerInstanceAbi
import Miri.Input.CompilerExternAbi

namespace Miri.Input.CompilerFunctionFacts
open Lean Miri.ABI Miri.Interpreter
structure Prepared where
  runtime : RuntimeMetadata
  program : LoweredProgram

def prepare (runtime : RuntimeMetadata) (program : LoweredProgram) : Except String Prepared :=
  pure ⟨runtime, program⟩

def signature (prepared : Prepared) (ty : MIR.TyId) : Except String (Nat × ABI.ExternAbi) := do
  let node ← prepared.runtime.node ty |>.mapError toString
  let some signature := node.signature | throw "function type has no source signature"
  return (signature.inputs.size, signature.abi)

def kind (prepared : Prepared) (ty : MIR.TyId) : Except String CallFunctionKind := do
  let node ← prepared.runtime.node ty |>.mapError toString
  match node.shape with
  | .functionPointer .. => return .FnPtr
  | .functionDefinition definition args _ _ => return .FnDef definition args
  | _ => throw "function-kind query on non-function type"

def pointerAbi (prepared : Prepared) (ty : MIR.TyId) (extra : Array MIR.TyId) : Except String (FnAbi MIR.TyId) := do
  let node ← prepared.runtime.node ty |>.mapError toString
  let .functionPointer signature _ := node.shape | throw "FnPtr ABI requested for non-pointer type"
  SourceAbiRuntime.ofSignature prepared.runtime signature extra

def hooks (prepared : Prepared) (extern : ABI.ExternAbi → Except String Extern)
    (base : CallHooks P S C E Other Extern (FnAbi MIR.TyId) (ArgAbi MIR.TyId)) :
    CallHooks P S C E Other Extern (FnAbi MIR.TyId) (ArgAbi MIR.TyId) :=
  { base with
    functionSignature := fun _ layout =>
      match signature prepared layout.ty >>= fun (count,abi) => return (count,← extern abi) with
      | .ok value => pure value | .error error => throw (.unsupported error)
    functionKind := fun ty => match kind prepared ty with
      | .ok value => pure value | .error error => throw (.unsupported error)
    fnAbiOfFnPtr := fun _ layout extra => match pointerAbi prepared layout.ty extra with
      | .ok value => pure value | .error error => throw (.unsupported error) }
/-- Production ExternAbi identity retains every pinned source variant/unwind
field, independently of the target canonical calling convention. -/
def concreteHooks (prepared : Prepared)
    (base : CallHooks P S C E Other ABI.ExternAbi (FnAbi MIR.TyId) (ArgAbi MIR.TyId)) :
    CallHooks P S C E Other ABI.ExternAbi (FnAbi MIR.TyId) (ArgAbi MIR.TyId) :=
  hooks prepared Except.ok base

end Miri.Input.CompilerFunctionFacts
