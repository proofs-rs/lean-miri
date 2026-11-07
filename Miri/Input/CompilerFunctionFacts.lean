import Miri.Input.RuntimeProgram
import Miri.Input.CompilerInstanceAbi
import Miri.Input.CompilerExternAbi

/-! `step.rs::eval_fn_call`: normalized original signature and function kind,
plus `fn_abi_of_fn_ptr` keyed by original function type and ordered extra types.
The ExternAbi remains the exact compiler payload; its interpretation is explicit.
No indirect runtime target is converted into a fabricated static instance. -/
namespace Miri.Input.CompilerFunctionFacts
open Lean Miri.ABI Miri.Interpreter
structure PointerAbi where
  ty : MIR.TyId
  extra : Array MIR.TyId
  result : Except String (FnAbi MIR.TyId)
structure Prepared where
  program : LoweredProgram
  functions : Array (Option FunctionQueryData)
  pointerAbis : Array PointerAbi
private def knownType (ctx : LowerContext) (id : Nat) : Except String Nat := do
  unless ctx.containsTypeId id do throw "function query references missing compiler type"
  pure id

def prepare (owner : RuntimeProgram)
    (abiCache : Option (CallResolution.FunctionAbiCache owner.runtime) := none) : Except String Prepared := do
  let program := owner.program
  let runtime := owner.runtime
  let ctx := LowerContext.ofDocument program.input
  let functions := program.input.mirTables.functions
  let mut abis := #[]
  for row in ← runtime.source.abiQueries.pointers do
    let ty := row.ty
    let some (some function) := functions[ty]? | throw "FnPtr ABI has no function-kind evidence"
    match function.kind with
    | .FnPtr => pure ()
    | _ => throw "FnPtr ABI query references a non-pointer function type"
    let extra := row.extra
    if abis.any (fun entry => entry.ty == ty && entry.extra == extra) then throw "duplicate FnPtr ABI query key"
    let result := row.abi.bind (fun id => CallResolution.functionAbiId runtime id abiCache)
    abis := abis.push ⟨ty,extra,result⟩
  pure ⟨program,functions,abis⟩

def signature (prepared : Prepared) (ty : MIR.TyId) : Except String (Nat × ABI.ExternAbi) := do
  let some (some entry) := prepared.functions[ty]? | throw "missing normalized original function signature"
  entry.signature

def kind (prepared : Prepared) (ty : MIR.TyId) : Except String CallFunctionKind := do
  let some (some entry) := prepared.functions[ty]? | throw "missing exact compiler function-kind query"
  pure entry.kind

def pointerAbi (prepared : Prepared) (ty : MIR.TyId) (extra : Array MIR.TyId) : Except String (FnAbi MIR.TyId) := do
  let some entry := prepared.pointerAbis.find? (fun e => e.ty == ty && e.extra == extra)
    | throw "missing exact function-pointer/extra-argument FnAbi query"
  entry.result

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
  hooks prepared pure base

end Miri.Input.CompilerFunctionFacts
