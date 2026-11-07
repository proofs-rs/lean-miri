import Miri.Input.CompilerScopes

/-! Compiler-owned call.rs constructors/drop queries. All keys use canonical
shared type IDs and complete instances. Absent evidence remains an error. -/
namespace Miri.Input.CompilerRuntimeQueries
open Lean Miri.Interpreter
structure TypeEntry where
  typeId : Nat
  pointerType : Nat
  referenceType : Nat
  dropGlue : Except String CallInstance
structure VirtualEntry where
  original : CallInstance
  methodDefinition : MIR.DefId
  parentTrait : MIR.DefId
  concreteType : Nat
  rebasedArgs : Array MIR.GenericArg
  resolved : Except String CallInstance
structure Prepared where
  program : LoweredProgram
  types : Array (Option TypeEntry)
  callerLocation : Array (CallInstance × Bool)
  virtualQueries : Array VirtualEntry
def prepare (program : LoweredProgram) : Except String Prepared := do
  let tables := program.input.mirTables
  let types : Array (Option TypeEntry) ← (← tables.runtimeTypes).mapIdxM fun id value => do
    let some value := value | pure none
    let drop := value.dropGlue.bind tables.instance
    pure (some ⟨id,value.pointerType,value.referenceType,drop⟩)
  let mut callers := #[]
  for entry in (← tables.runtimeInstances) do
    let callee ← tables.instance entry.instanceId
    let track := entry.callerLocation
    if let some (_,prior) := callers.find? (·.1 == callee) then
      unless prior == track do throw "conflicting full-instance caller-location query"
    else callers := callers.push (callee,track)
  let virtualQueries : Array VirtualEntry ← (← tables.runtimeVirtual).mapM fun query => do
    let original ← tables.instance query.original
    let resolved := query.resolved.bind tables.instance
    pure ⟨original,query.methodDefinition,query.parentTrait,query.concreteType,query.rebasedArgs,resolved⟩
  pure ⟨program,types,callers,virtualQueries⟩
private def entry (prepared : Prepared) (id : Nat) : Except String TypeEntry := do
  let some (some entry) := prepared.types[id]? | throw "missing exact compiler runtime type query"
  pure entry

def mutPointerType (prepared : Prepared) (id : Nat) : Except String Nat :=
  return (← entry prepared id).pointerType

def mutReferenceType (prepared : Prepared) (id : Nat) : Except String Nat :=
  return (← entry prepared id).referenceType

def resolveDropGlue (prepared : Prepared) (id : Nat) : Except String CallInstance := do
  (← entry prepared id).dropGlue

def requiresCallerLocation (prepared : Prepared) (callee : CallInstance) : Except String Bool := do
  let some (_,track) := prepared.callerLocation.find? (·.1 == callee)
    | throw "missing exact full-instance caller-location query"
  pure track
def parentTrait (prepared : Prepared) (method : MIR.DefId) : Except String MIR.DefId := do
  let matching := prepared.virtualQueries.filter (·.methodDefinition == method)
  let some first := matching[0]? | throw "missing exact virtual parent-trait query"
  unless matching.all (·.parentTrait == first.parentTrait) do throw "conflicting parent-trait queries"
  pure first.parentTrait

def rebaseVirtualArgs (prepared : Prepared) (args : Array MIR.GenericArg)
    (parent : MIR.DefId) (concrete : Nat) : Except String (Array MIR.GenericArg) := do
  let matching := prepared.virtualQueries.filter fun entry =>
    entry.original.args == args && entry.parentTrait == parent && entry.concreteType == concrete
  let some first := matching[0]? | throw "missing complete-key virtual rebase query"
  unless matching.all (·.rebasedArgs == first.rebasedArgs) do throw "conflicting virtual rebase queries"
  pure first.rebasedArgs

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
    mutPointerType := fun ty => lift (mutPointerType prepared ty)
    mutReferenceType := fun ty => lift (mutReferenceType prepared ty)
    resolveDropGlue := fun ty => lift (resolveDropGlue prepared ty)
    requiresCallerLocation := fun callee => lift (requiresCallerLocation prepared callee)
    parentTrait := fun method => lift (parentTrait prepared method)
    rebaseVirtualArgs := fun args parent concrete => lift (rebaseVirtualArgs prepared args parent concrete)
    expectResolveForVTable := fun _ method args => lift (expectResolveForVTable prepared method args) }
end Miri.Input.CompilerRuntimeQueries
