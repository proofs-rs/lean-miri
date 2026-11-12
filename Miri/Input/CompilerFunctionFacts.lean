import Miri.Input.CompilerInstanceAbi
import Miri.Input.CompilerExternAbi

/-! `step.rs::eval_fn_call`: normalized original signature and function kind,
plus `fn_abi_of_fn_ptr` keyed by original function type and ordered extra types.
The ExternAbi remains the exact compiler payload; its interpretation is explicit.
No indirect runtime target is converted into a fabricated static instance. -/
namespace Miri.Input.CompilerFunctionFacts
open Lean Miri.ABI Miri.Interpreter

structure Function where
  ty : MIR.TyId
  instanceId : Option CallInstance
  signature : Except String (Nat × ABI.ExternAbi)
structure PointerAbi where
  ty : MIR.TyId
  extra : Array MIR.TyId
  result : Except String Nat
structure Prepared where
  runtime : RuntimeMetadata
  program : LoweredProgram
  functions : Array Function
  pointerAbis : Array PointerAbi
private def liftWorld (value : Except String A) : TypeArena.WorldM A :=
  match value with | .ok result => pure result | .error message => throw message

/-- `step.rs` distinguishes nominal FnDef identity from FnPtr directly from
TyKind. Signature metadata and a prior instance-resolution answer are not keys. -/
def kindInWorld (_prepared : Prepared) (ty : MIR.TyId) : TypeArena.WorldM CallFunctionKind := do
  let world ← get
  match ← liftWorld (world.lookupType ty) with
  | .material node => match node.shape with
    | .functionDefinition definition arguments _ _ variables =>
      unless variables.isEmpty do throw "FnDef call arguments retain a nonempty binder"
      pure (.FnDef definition arguments)
    | .functionPointer .. => pure .FnPtr
    | _ => throw "call function type is neither FnDef nor FnPtr"
  | .constructed (.functionDefinition definition arguments variables) =>
    unless variables.isEmpty do throw "FnDef call arguments retain a nonempty binder"
    pure (.FnDef (← liftWorld (world.definitionRef definition)) arguments)
  | .constructed _ => throw "call function type is neither FnDef nor FnPtr"
private def knownType (ctx : LowerContext) (id : Nat) : Except String Nat := do
  unless ctx.containsTypeId id do throw "function query references missing compiler type"
  pure id
def prepare (runtime : RuntimeMetadata) (program : LoweredProgram) : Except String Prepared := do
  let source := program.input.queries.functionFacts
  let ctx := LowerContext.ofDocument program.input
  let tables := program.compilerTables
  let mut functions := #[]
  for record in source.types do
    let ty ← knownType ctx record.typeId
    if functions.any (fun f => f.ty == ty) then throw "duplicate compiler function type query"
    let inst ← record.instanceId.mapM fun id => do
      let _ ← CompilerInstance.source ctx.instances id
      pure id
    let signature := do
      for input in record.signature.inputs do
        let _ ← knownType ctx input
      pure (record.signature.inputs.size, record.signature.abi)
    functions := functions.push ⟨ty, inst, signature⟩
  let mut abis := #[]
  for record in source.pointerAbis do
    let ty ← knownType ctx record.typeId
    let some function := functions.find? (fun f => f.ty == ty) | throw "FnPtr ABI has no function-kind evidence"
    unless function.instanceId.isNone do throw "FnPtr ABI query references a non-pointer function type"
    let extra ← record.extraArgumentTypes.mapM (knownType ctx)
    if abis.any (fun entry => entry.ty == ty && entry.extra == extra) then throw "duplicate FnPtr ABI query key"
    abis := abis.push ⟨ty, extra, .ok record.abiId⟩
  pure ⟨runtime,program.withCompilerTables tables,functions,abis⟩

def signature (prepared : Prepared) (ty : MIR.TyId) : Except String (Nat × ABI.ExternAbi) := do
  let some entry := prepared.functions.find? (fun f => f.ty == ty) | throw "missing normalized original function signature"
  entry.signature

def kind (prepared : Prepared) (ty : MIR.TyId) : Except String CallFunctionKind := do
  let some entry := prepared.functions.find? (fun f => f.ty == ty) | throw "missing exact compiler function-kind query"
  match entry.instanceId with
  | none => pure .FnPtr
  | some inst =>
    let instances := prepared.program.input.instances
    let kind ← CompilerInstance.kindOf instances inst
    match kind with
    | .Item definition => return .FnDef definition (← CompilerInstance.argsOf instances inst)
    | _ => throw "FnDef compiler type did not contain its exact Item definition"

def pointerAbi (prepared : Prepared) (ty : MIR.TyId) (extra : Array MIR.TyId) : Except String (FnAbi MIR.TyId) := do
  let some entry := prepared.pointerAbis.find? (fun e => e.ty == ty && e.extra == extra)
    | throw "missing exact function-pointer/extra-argument FnAbi query"
  CallResolution.functionAbiId prepared.runtime (← entry.result)

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
