import Miri.Input.LowerMIR
import Miri.Input.CompilerInstanceAbi
import Miri.Input.CompilerExternAbi
import Miri.Input.WorldFunctionPointerAbi

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

private def kindAt (world : TypeArena.World) (ty : MIR.TyId) : Except String CallFunctionKind := do
  match ← world.lookupType ty with
  | .material node => match node.shape with
    | .functionDefinition definition arguments _ _ variables =>
      unless variables.isEmpty do throw "FnDef call arguments retain a nonempty binder"
      pure (.FnDef definition arguments)
    | .functionPointer .. => pure .FnPtr
    | _ => throw "call function type is neither FnDef nor FnPtr"
  | .constructed (.functionPointer _) => pure .FnPtr
  | .constructed (.functionDefinition definition arguments variables) =>
    unless variables.isEmpty do throw "FnDef call arguments retain a nonempty binder"
    pure (.FnDef (← world.definitionRef definition) arguments)
  | .constructed _ => throw "call function type is neither FnDef nor FnPtr"

/-- `step.rs` distinguishes nominal FnDef identity from FnPtr directly from
TyKind. Signature metadata and a prior instance-resolution answer are not keys. -/
def kindInWorld (_prepared : Prepared) (ty : MIR.TyId) : TypeArena.WorldM CallFunctionKind := do
  liftWorld (kindAt (← get) ty)
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
      let _ ← CompilerInstance.Material.source ctx.instances id
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

/-- Structural function kind in the current execution type universe. -/
def kind (_prepared : Prepared) (world : RuntimeArrayTypes.World) (ty : MIR.TyId) : Except String CallFunctionKind :=
  kindAt world.arena ty

def pointerAbi (prepared : Prepared) (ty : MIR.TyId) (extra : Array MIR.TyId) : Except String (FnAbi MIR.TyId) := do
  let some entry := prepared.pointerAbis.find? (fun e => e.ty == ty && e.extra == extra)
    | throw "missing exact function-pointer/extra-argument FnAbi query"
  CallResolution.functionAbiId prepared.runtime (← entry.result)

/-- A constructed FnPtr has its own source signature; normalized answer rows
are only an exact residual for unchanged material types. -/
def signatureInWorld (prepared : Prepared) (ty : MIR.TyId) :
    RuntimeArrayTypes.CompilerM (Nat × ABI.ExternAbi) := do
  let world ← get
  match WorldFunctionPointerAbi.sourceSignature world.arena ty with
  | .ok signature => pure (signature.inputs.size,signature.abi)
  | .error sourceError =>
    match world.arena.lookupType ty with
    | .ok (.material _) =>
      match signature prepared ty with | .ok value => pure value | .error error => throw error
    | _ => throw s!"{sourceError}; constructed function type has no signature residual"

/-- Source FnPtr ABI in the current World. Only an unchanged material source
constructor and material extra keys may consult an exact residual row. -/
def pointerAbiInWorld (prepared : Prepared) (ty : MIR.TyId) (extra : Array MIR.TyId) :
    RuntimeArrayTypes.CompilerM (FnAbi MIR.TyId) := do
  let world ← get
  match (WorldFunctionPointerAbi.construct ty extra).run world with
  | .ok (abi,after) => set after; pure abi
  | .error sourceError =>
    let residual : Except String (FnAbi MIR.TyId) := do
      let .material source ← world.arena.lookupType ty
        | throw "constructed FnPtr has no imported ABI query"
      let some original := prepared.runtime.source.types[ty]?
        | throw "FnPtr material source absent"
      unless source.id == ty && (← world.arena.materialKey source) == (← world.arena.materialKey original) do
        throw "FnPtr material source differs from execution World"
      for id in extra do
        let .material source ← world.arena.lookupType id
          | throw "constructed extra type has no imported FnPtr ABI query"
        let some original := prepared.runtime.source.types[id]?
          | throw "FnPtr extra material source absent"
        unless source.id == id && (← world.arena.materialKey source) == (← world.arena.materialKey original) do
          throw "FnPtr extra material source differs from execution World"
      pointerAbi prepared ty extra
    match residual with
    | .ok abi => pure abi
    | .error error => throw s!"{sourceError}; {error}"

def hooks (prepared : Prepared) (types : RuntimeArrayQueries.Access S) (extern : ABI.ExternAbi → Except String Extern)
    (base : CallHooks P S C E Other Extern (FnAbi MIR.TyId) (ArgAbi MIR.TyId)) :
    CallHooks P S C E Other Extern (FnAbi MIR.TyId) (ArgAbi MIR.TyId) :=
  { base with
    functionSignature := fun _ layout => do
      let (count,abi) ← RuntimeArrayQueries.performCompiler types (signatureInWorld prepared layout.ty)
      match extern abi with
      | .ok abi => pure (count,abi) | .error error => throw (.unsupported error)
    functionKind := fun ty => do
      match kind prepared (← RuntimeArrayQueries.compilerSnapshot types) ty with
      | .ok value => pure value | .error error => throw (.unsupported error)
    fnAbiOfFnPtr := fun _ layout extra =>
      RuntimeArrayQueries.performCompiler types (pointerAbiInWorld prepared layout.ty extra) }
/-- Production ExternAbi identity retains every pinned source variant/unwind
field, independently of the target canonical calling convention. -/
def concreteHooks (prepared : Prepared) (types : RuntimeArrayQueries.Access S)
    (base : CallHooks P S C E Other ABI.ExternAbi (FnAbi MIR.TyId) (ArgAbi MIR.TyId)) :
    CallHooks P S C E Other ABI.ExternAbi (FnAbi MIR.TyId) (ArgAbi MIR.TyId) :=
  hooks prepared types Except.ok base

end Miri.Input.CompilerFunctionFacts
