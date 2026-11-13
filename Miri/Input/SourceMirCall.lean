import Miri.Input.SourceMir
import Miri.Input.SourceCall
import Miri.Input.GenericInstantiationWorld
import Miri.Input.CompilerInstance
import Miri.Input.WorldObjectCandidate

/-! Symbolic source-call sites. Reading a seed never instantiates a MIR body or
looks up an ABI. Resolution takes effectful callbacks belonging to the current
execution's one type/instance universe. -/
namespace Miri.Input.SourceMirCall
open GenericSubstitution

structure Seed where
  expression : Term
  arguments : Array Miri.MIR.GenericArg
  constantSpan : Miri.MIR.SpanRef
  deriving Repr

/-- Source-only accessor; material call sites use their existing provider. -/
def source (document : ImportDocument) (bodyIndex blockIndex : Nat) : Except String (Option Seed) := do
  let some body := document.bodies[bodyIndex]? | throw "canonical body index is absent"
  let .copyTemplate reference := body | return none
  let _ ← SourceMir.metadata document bodyIndex
  let some source := document.mirTemplates[reference.templateId]?
    | throw "generic MIR source template is absent"
  let some block := source.template.skeleton.blocks[blockIndex]?
    | throw "source call block is absent"
  let (functionType,constantSpan) ← match block.terminator.kind with
    | .call functionType constantSpan .. | .sourceCall functionType constantSpan .. => pure (functionType,constantSpan)
    | _ => return none
  let some expression := source.template.types[functionType.index]?
    | throw "source call function type slot is absent"
  pure (some ⟨expression,reference.genericArgs,constantSpan⟩)

/-- Read a symbolic call from this execution's exact body namespace. -/
def sourceIdentity (identity : Miri.Interpreter.BodyIdentity) (blockIndex : Nat) :
    RuntimeArrayTypes.CompilerM (Option Seed) := do
  let world ← get
  let view ← match world.bodies.lookup identity.index with
    | .ok view => pure view | .error error => throw error
  match view with
  | .material index =>
    match source world.metadata.source index blockIndex with
    | .ok value => pure value | .error error => throw error
  | .constructed (.fnPointerShim _) => pure none
  | .constructed (.template key) =>
    let _ ← SourceMir.metadataIdentity identity
    let some template := world.metadata.source.mirTemplates[key.templateId]?
      | throw "generic MIR source template is absent"
    let some block := template.template.skeleton.blocks[blockIndex]?
      | throw "source call block is absent"
    let (functionType,constantSpan) ← match block.terminator.kind with
      | .call functionType constantSpan .. | .sourceCall functionType constantSpan .. => pure (functionType,constantSpan)
      | _ => return none
    let some expression := template.template.types[functionType.index]?
      | throw "source call function type slot is absent"
    pure (some ⟨expression,key.instanceKey.arguments,constantSpan⟩)

private def liftPure {m : Type → Type} [Monad m] [MonadExceptOf String m]
    (result : Except String α) : m α :=
  match result with | .ok value => pure value | .error message => throw message

/-- No query-answer cache or private arena is created here. Both argument and
FnDef interning effects flow through the caller's same monad. -/
def resolveWith {m : Type → Type} [Monad m] [MonadExceptOf String m]
    (ofArguments : Array Miri.MIR.GenericArg → m (Array Term))
    (resolveDefinition : DefinitionIdentity → m DefinitionRef)
    (resolveType : Term → m TypeId)
    (resolveInstance : DefinitionRef → Array Miri.MIR.GenericArg → m InstanceId)
    (seed : Seed) : m (SourceCall.Resolution × Miri.MIR.Operand) := do
  let arguments ← ofArguments seed.arguments
  let expression ← liftPure (GenericSubstitution.instantiate 16384 arguments seed.expression)
  let expression ← liftPure (MirTemplate.eraseFreeRegions 16384 expression)
  liftPure (MirTemplate.validateClosed 16384 expression)
  let callee ← liftPure (SourceCall.calleeOfFunctionTerm expression)
  let resolution ← SourceCall.resolveCalleeWith resolveDefinition resolveType resolveInstance callee
  let function := Miri.MIR.Operand.Constant {
    span := seed.constantSpan, userType := none,
    value := .Val .ZeroSized resolution.functionType }
  pure (resolution,function)

/-- Resolve in the current execution's universe. Dynamic trait Self uses source object-candidate selection;
other callees retain Item construction. Body and ABI remain separate capabilities. -/
def resolveInWorld (_document : ImportDocument) (seed : Seed) :
    RuntimeArrayTypes.CompilerM (SourceCall.Resolution × Miri.MIR.Operand) :=
  resolveWith
    (fun arguments => do liftPure (GenericInstantiationWorld.ofArguments (← get).arena 16384 arguments))
    (fun definition => do liftPure ((← get).arena.definitionRef definition))
    (fun term => RuntimeArrayTypes.liftType (GenericInstantiationWorld.resolveType 16384 term))
    (WorldObjectCandidate.resolveOrdinary 100000 16384) seed

end Miri.Input.SourceMirCall
