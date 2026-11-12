import Miri.Input.CompilerScopes
import Miri.Input.TypeArena
import Miri.Input.GenericRebase

/-! Compiler-owned call.rs constructors/drop queries. All keys use canonical
shared type IDs and complete instances. Absent evidence remains an error. -/
namespace Miri.Input.CompilerRuntimeQueries
open Lean Miri.Interpreter
structure TypeEntry where
  typeId : Nat
  dropGlue : Except String CallInstance
structure VirtualEntry where
  original : CallInstance
  methodDefinition : MIR.DefId
  parentTrait : MIR.DefId
  concreteType : Nat
  parentGenericCount : Nat
  rebasedArgs : Array MIR.GenericArg
  resolved : Except String CallInstance
structure Prepared where
  program : LoweredProgram
  types : Array TypeEntry
  virtualQueries : Array VirtualEntry
private def typeId (ctx : LowerContext) (id : Nat) : Except String Nat := do
  unless ctx.containsTypeId id do throw "runtime query references absent compiler type"
  pure id

def prepare (program : LoweredProgram) : Except String Prepared := do
  let raw := program.input.queries.runtime
  let ctx := LowerContext.ofDocument program.input
  let tables := program.compilerTables
  let mut types := #[]
  for entry in raw.types do
    let id ← typeId ctx entry.inputType
    let drop : Except String CallInstance := match entry.dropGlue with
      | none => .error "drop glue compiler instance absent"
      | some id => (CompilerInstance.source ctx.instances id).map fun _ => id
    unless !(types.any (·.typeId == id)) do throw "duplicate compiler runtime type query"
    types := types.push ⟨id, drop⟩
  let mut virtualQueries := #[]
  for query in raw.virtualQueries do
    let original := query.originalInstance
    let _ ← CompilerInstance.source ctx.instances original
    unless query.methodDefinition < tables.definitions.size && query.parentTrait < tables.definitions.size do
      throw "compiler definition ID out of bounds"
    let concrete ← typeId ctx query.concreteType
    let args ← CompilerInstance.argsOf ctx.instances original
    let rebound ← GenericRebase.virtualSelf args query.parentGenericCount concrete
    let resolved := (CompilerInstance.source ctx.instances query.resolved).map fun _ => query.resolved
    virtualQueries := virtualQueries.push ⟨original, query.methodDefinition, query.parentTrait,
      concrete, query.parentGenericCount, rebound, resolved⟩
  pure ⟨program, types, virtualQueries⟩
private def entry (prepared : Prepared) (id : Nat) : Except String TypeEntry := do
  let some entry := prepared.types.find? (·.typeId == id)
    | throw "missing exact compiler runtime type query"
  pure entry

/-- Port of rustc_middle/ty/sty.rs mutable pointer/reference constructors.
Material identities are reused; absent constructor nodes are interned in the
input-relative lazy arena and receive genuinely new type identities. -/
def internConstructor := TypeArena.intern

def mutPointerType (prepared : Prepared) (id : Nat) : Except String Nat :=
  TypeArena.intern prepared.program.input.types id false

def mutReferenceType (prepared : Prepared) (id : Nat) : Except String Nat :=
  TypeArena.intern prepared.program.input.types id true

def resolveDropGlue (prepared : Prepared) (id : Nat) : Except String CallInstance := do
  (← entry prepared id).dropGlue

/-- Pinned rustc ty/instance.rs::InstanceKind::requires_caller_location.
Only Item, Virtual and VTable consult the definition's body codegen attributes;
ClosureOnce stores its own flag and every other instance kind returns false. -/
def instanceRequiresCallerLocation (definitions : Array DefinitionId)
    (kind : CallInstanceKind) : Except String Bool := do
  match kind with
  | .Item definition | .Virtual definition _ | .Shim (.VTable definition) =>
    let some material := definitions[definition]?
      | throw "caller-location definition material absent"
    let some flag := material.bodyTrackCaller
      | throw "caller-location body codegen attribute material absent"
    pure flag
  | .Shim (.ClosureOnce _ _ trackCaller) => pure trackCaller
  | _ => pure false

def requiresCallerLocation (prepared : Prepared) (callee : CallInstance) : Except String Bool := do
  instanceRequiresCallerLocation prepared.program.input.definitions
    (← CompilerInstance.kindOf prepared.program.input.instances callee)

def parentTrait (prepared : Prepared) (method : MIR.DefId) : Except String MIR.DefId := do
  let matching := prepared.virtualQueries.filter (·.methodDefinition == method)
  let some first := matching[0]? | throw "missing exact virtual parent-trait query"
  unless matching.all (·.parentTrait == first.parentTrait) do throw "conflicting parent-trait queries"
  pure first.parentTrait

def rebaseVirtualArgs (prepared : Prepared) (args : Array MIR.GenericArg)
    (parent : MIR.DefId) (concrete : Nat) : Except String (Array MIR.GenericArg) := do
  let matching := prepared.virtualQueries.filter (·.parentTrait == parent)
  let some first := matching[0]? | throw "virtual trait generic definition material absent"
  unless matching.all (·.parentGenericCount == first.parentGenericCount) do
    throw "conflicting virtual trait generic definition material"
  let _ ← TypeArena.node prepared.program.input.types concrete
  GenericRebase.virtualSelf args first.parentGenericCount concrete

def expectResolveForVTable (prepared : Prepared) (method : MIR.DefId)
    (args : Array MIR.GenericArg) : Except String CallInstance := do
  let matching := prepared.virtualQueries.filter fun entry =>
    entry.methodDefinition == method && entry.rebasedArgs == args
  let some first := matching[0]? | throw "missing complete-key virtual resolution query"
  let callee ← first.resolved
  for entry in matching do
    unless (← entry.resolved) == callee do throw "conflicting virtual resolutions"
  pure callee
private def lift (result : Except String A) : EStateM StepError S A :=
  match result with
  | .ok result => pure result
  | .error error => throw (.invalidProgram error)

def hooks (prepared : Prepared) (base : VirtualCalls.CompilerHooks S C) :
    VirtualCalls.CompilerHooks S C :=
  { base with
    instanceArgs := fun inst => lift (CompilerInstance.argsOf
      prepared.program.input.instances inst)
    mutPointerType := fun ty => lift (mutPointerType prepared ty)
    mutReferenceType := fun ty => lift (mutReferenceType prepared ty)
    resolveDropGlue := fun ty => lift (resolveDropGlue prepared ty)
    requiresCallerLocation := fun callee => lift (requiresCallerLocation prepared callee)
    parentTrait := fun method => lift (parentTrait prepared method)
    rebaseVirtualArgs := fun args parent concrete => lift (rebaseVirtualArgs prepared args parent concrete)
    expectResolveForVTable := fun _ method args => lift (expectResolveForVTable prepared method args) }
end Miri.Input.CompilerRuntimeQueries
