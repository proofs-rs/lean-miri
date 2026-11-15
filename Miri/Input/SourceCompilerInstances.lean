import Miri.Input.SourceCompilerWorld
import Miri.Interpreter.Step
import Miri.Interpreter.ExecutionCallLeaves

/-! Persistent source Item construction at interpreter query sites. No call-site
callee/instance answer, frozen Prepared array or name-based selection is read.
Unsupported trait/associated selection is distinct from free-function identity. -/
namespace Miri.Input.SourceCompilerInstances
open Miri.Interpreter

private def query (result : Except String α) : EStateM StepError S α :=
  match result with | .ok value => pure value | .error error => throw (.unsupported error)

private def current (access : SourceCompilerWorld.Access S) : EStateM StepError S SourceCompilerWorld.World := do
  let some world := access.get (← get) | throw (.unsupported "source compiler World is unavailable")
  return world

def instanceKind (access : SourceCompilerWorld.Access S) (callee : CallInstance) :
    EStateM StepError S CallInstanceKind := do
  return (← query (SourceCompilerWorld.node (← current access) callee)).instanceKind

/-- Pointwise proof boundary for the live kind query. The selected current
World supplies the actual node; absent World and invalid node failures retain
the incoming state just as successful lookup does. No prepared row is read. -/
theorem instanceKind_at (access : SourceCompilerWorld.Access S) (before : S) (callee : CallInstance) :
    instanceKind access callee before =
      match access.get before with
      | none => .error (.unsupported "source compiler World is unavailable") before
      | some world => match SourceCompilerWorld.node world callee with
        | .error reason => .error (.unsupported reason) before
        | .ok node => .ok node.instanceKind before := by
  cases present : access.get before with
  | none =>
    simp [instanceKind,current,query,present,get,getThe,MonadStateOf.get,EStateM.get,
      bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]
    with_unfolding_all rfl
  | some world =>
    cases lookup : SourceCompilerWorld.node world callee <;>
      simp [instanceKind,current,query,present,lookup,get,getThe,MonadStateOf.get,EStateM.get,
        bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure] <;> with_unfolding_all rfl

def instanceArgs (access : SourceCompilerWorld.Access S) (callee : CallInstance) :
    EStateM StepError S (Array MIR.GenericArg) := do
  return (← query (SourceCompilerWorld.node (← current access) callee)).genericArgs

/-- Original FnDef identity comes from the current type shape, not a catalog
row naming an already resolved method/shim. -/
def functionKind (access : SourceCompilerWorld.Access S) (typeId : MIR.TyId) :
    EStateM StepError S CallFunctionKind := do
  let world ← current access
  let some row := world.canonical.types[typeId]? | throw (.unsupported "source function type absent")
  unless row.id == typeId do throw (.unsupported "source function type identity mismatch")
  match row.shape with
  | .functionDefinition definition arguments _ _ => return .FnDef definition arguments
  | .functionPointer _ _ => return .FnPtr
  | _ => throw (.unsupported "source function kind requested for non-function type")

private def checkSlots (world : SourceCompilerWorld.World)
    (parameters : Array SourceCompilerWorld.ParameterKind) (arguments : Array MIR.GenericArg) : Except String Unit := do
  unless parameters.size == arguments.size do throw "source free Item generic argument count mismatch"
  for (parameter,argument) in parameters.zip arguments do
    match parameter,argument with
    | .region,.Lifetime _ => pure ()
    | .typeParameter,.Type id =>
      let some type := world.canonical.types[id]? | throw "source free Item type argument absent"
      unless type.id == id do throw "source free Item type argument identity mismatch"
    | .constParameter,.Const id =>
      unless id < world.canonical.typeConstants.size do throw "source free Item constant argument absent"
    | _,_ => throw "source free Item generic argument kind mismatch"

/-- `Instance::new_raw(Item,args)` for a source-confirmed free function. Source
material validates kind/slots even for existing keys. Classic input without source
can only reuse an identical existing raw Item key at its original trust boundary;
it cannot construct a new key or choose a trait implementation. Identity
availability supplies no body/ABI/trait-obligation capability. -/
def itemInstance (access : SourceCompilerWorld.Access S) (definition : MIR.DefId)
    (arguments : Array MIR.GenericArg) : EStateM StepError S CallInstance := do
  let state ← get
  let some world := access.get state | throw (.unsupported "source compiler World is unavailable")
  let some raw := world.canonical.definitions[definition]? | throw (.unsupported "source free Item DefId absent")
  let key : SourceCompilerWorld.InstanceKey := ⟨raw,arguments⟩
  if world.canonical.sourceMaterial.isNone then
    -- Existing classic input is its own trust boundary. Reuse only the
    -- identical raw Item key; never choose another implementation/new key.
    let some callee := SourceCompilerWorld.findItem world key
      | throw (.unsupported "source declaration unavailable for new Item key")
    let original ← query (SourceCompilerWorld.keyOf world callee)
    unless original == key do throw (.unsupported "legacy canonical Item key contradiction")
    return callee
  let some material := world.canonical.sourceMaterial | throw (.unsupported "typed source material absent")
  let declarations := material.declarations.filter (·.definition == raw)
  unless declarations.size == 1 do throw (.unsupported "typed source Item declaration missing or ambiguous")
  let some declaration := declarations[0]? | throw (.unsupported "typed source Item declaration absent")
  unless declaration.definition == raw && declaration.kind == .function do
    throw (.unsupported "source associated/trait Item selection unsupported")
  unless declaration.role == .ordinary do
    throw (.unsupported "source intrinsic/drop-glue/foreign or unavailable function role requires a separate resolver")
  query (checkSlots world declaration.parameters arguments)
  let (updated,callee) ← query (SourceCompilerWorld.internItem #[declaration] world key)
  set (access.put state updated)
  return callee

end Miri.Input.SourceCompilerInstances
