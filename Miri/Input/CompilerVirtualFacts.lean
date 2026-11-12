import Miri.Input.RuntimeArrayQueries
import Miri.Input.CompilerFactAdapters
import Miri.Input.CompilerVTableFacts
import Miri.Input.CompilerScopes
import Miri.Input.CompilerRuntimeQueries
import Miri.Interpreter.VirtualCalls

/-! Bind only exported, exact compilation-local compiler query evidence to
runtime virtual-call drivers. Unexported trait-principal/instance-rebasing/drop
queries remain required leaves in the original dictionary. -/
namespace Miri.Input.CompilerVirtualFacts
open Miri.ABI Miri.Interpreter
abbrev Result := Except String

def receiverKind (context : CompilerFacts.Context) (id : TypeId) : Result VirtualCalls.ReceiverKind := do
  let node ← context.runtime.node id |>.mapError toString
  match node.shapeKind with
  | .reference => pure .reference
  | .rawPointer => pure .rawPointer
  | .dynamicTraitObject => pure .dynamic
  | _ => pure .other

/-- Dynamic metadata owns its predicate sequence; each element names the
canonical predicate pool and the principal retains its exact compiler ID. -/
def dynamicData (prepared : CompilerFactAdapters.Prepared) (id : TypeId) :
    Result (Option VirtualCalls.DynamicData) := do
  let node ← prepared.context.runtime.node id |>.mapError toString
  match node.shape with
  | .dynamicTraitObject predicates principal _ => pure (some ⟨predicates,principal⟩)
  | _ => pure none

private def liftWorld (value : Result A) : TypeArena.WorldM A :=
  match value with | .ok result => pure result | .error message => throw message

def receiverKindInWorld (context : CompilerFacts.Context) (id : TypeId) :
    TypeArena.WorldM VirtualCalls.ReceiverKind := do
  match ← RuntimeMetadata.shapeKindInWorld context.runtime id with
  | .reference => pure .reference | .rawPointer => pure .rawPointer
  | .dynamicTraitObject => pure .dynamic | _ => pure .other

def dynamicDataInWorld (_prepared : CompilerFactAdapters.Prepared) (id : TypeId) :
    TypeArena.WorldM (Option VirtualCalls.DynamicData) := do
  match ← liftWorld ((← get).lookupType id) with
  | .material node => match node.shape with
    | .dynamicTraitObject predicates principal _ => pure (some ⟨predicates,principal⟩)
    | _ => pure none
  | .constructed _ => pure none

def builtinDerefInWorld (context : CompilerFacts.Context) (id : TypeId) :
    TypeArena.WorldM (Option TypeId) := do
  let world ← get
  match ← liftWorld (world.lookupType id) with
  | .material _ => liftWorld (CompilerFacts.builtinDeref context id true)
  | .constructed (.reference pointee ..) | .constructed (.rawPointer pointee _) => pure (some pointee)
  | .constructed (.adt definition arguments) =>
    let reference ← liftWorld (world.definitionRef definition)
    let some source := world.definitions[reference]? | throw "ADT source declaration absent"
    let some declaration := source.adtDeclaration | throw "ADT source declaration absent"
    if declaration.langItem != some "owned_box" then return none
    let some (Miri.MIR.GenericArg.Type pointee) := arguments[0]?
      | throw "Box source type argument absent"
    pure (some pointee)
  | .constructed _ => pure none

private def lift (value : Result A) : EStateM StepError S A :=
  match value with
  | .ok value => pure value
  | .error error => throw (.unsupported s!"compiler virtual call query: {error}")

/-- Every installed query is backed by an actual fully-monomorphized compiler
record or canonical type/layout evidence. This does not solve instances or
construct a raw-pointer/ref type by searching for a same-sized layout. -/
def compilerHooks (prepared : CompilerFactAdapters.Prepared) (types : RuntimeArrayQueries.Access S)
    (base : VirtualCalls.CompilerHooks S C) : VirtualCalls.CompilerHooks S C :=
  { base with
    classifyReceiver := fun ty => RuntimeArrayQueries.perform types (receiverKindInWorld prepared.context ty)
    dynamicData := fun ty => RuntimeArrayQueries.perform types (dynamicDataInWorld prepared ty)
    fieldLayout := fun layout index => RuntimeArrayQueries.perform types (RuntimeMetadata.fieldLayoutForInWorld prepared.context.runtime layout index)
    structTailForCodegen := fun ty => RuntimeArrayQueries.perform types (RuntimeMetadata.metadataTailInWorld prepared.context.runtime ty)
    builtinDeref := fun ty => RuntimeArrayQueries.perform types (builtinDerefInWorld prepared.context ty)
    layoutOf := fun ty => RuntimeArrayQueries.perform types (RuntimeMetadata.layoutInWorld prepared.context.runtime ty)
    unitLayout := lift (CompilerFacts.unitLayout prepared.context) }

/-- Construction validates all inlinecallee evidence, including unused instances.
An absent full instance delegates to the mandatory base query. -/
def inlineAttribute (prepared : CompilerScopes.Prepared) (fnInstance : CallInstance) : Option Bool :=
  prepared.inlineAttributes[fnInstance]?

/-- The canonical body key comes directly from the saved frame. Body equality
is only a consistency assertion after indexing, never a body lookup strategy.
A non-inlined instance's attribute still uses the mandatory base query. -/
def scopeHooks (prepared : CompilerScopes.Prepared) (types : RuntimeArrayQueries.Access S)
    (base : VirtualCalls.CompilerHooks S C) :
    VirtualCalls.CompilerHooks S C :=
  { base with
    sourceScope := fun identity _ body scope => do
      let actual ← RuntimeArrayQueries.performCompiler types (prepared.program.resolveBodyIdentity identity)
      unless actual.body == body do throw (.invalidProgram "frame body identity/content mismatch")
      RuntimeArrayQueries.performCompiler types (CompilerScopes.sourceScopeIdentity prepared identity scope)
    requiresCallerLocation := fun fnInstance => do
      match inlineAttribute prepared fnInstance with
      | some value => pure value
      | none => base.requiresCallerLocation fnInstance }

/-- Actual compiler Ty::new_mut_ptr/new_mut_ref, resolve_drop_glue and
requires_caller_location evidence. Missing keys fail; no structural type search
or synthetic function/ABI is introduced. -/
def runtimeHooks (prepared : CompilerRuntimeQueries.Prepared) (types : RuntimeArrayQueries.Access S)
    (base : VirtualCalls.CompilerHooks S C) :
    VirtualCalls.CompilerHooks S C :=
  { base with
    mutPointerType := fun ty => RuntimeArrayQueries.perform types (CompilerRuntimeQueries.mutPointerType prepared ty)
    mutReferenceType := fun ty => RuntimeArrayQueries.perform types (CompilerRuntimeQueries.mutReferenceType prepared ty)
    resolveDropGlue := fun ty => RuntimeArrayQueries.perform types (CompilerRuntimeQueries.resolveDropGlue prepared ty)
    requiresCallerLocation := fun fnInstance => RuntimeArrayQueries.performCompiler types (CompilerRuntimeQueries.requiresCallerLocation prepared fnInstance) }

/-- Both type and vtable trait predicates consume the same compiler predicate
array table; no principal identity is synthesized from a diagnostic string. -/
def hooks (prepared : CompilerFactAdapters.Prepared) (types : RuntimeArrayQueries.Access S)
    (base : VirtualCalls.Hooks P S C E) :
    VirtualCalls.Hooks P S C E :=
  { base with
    compiler := compilerHooks prepared types base.compiler
    vtable := CompilerVTableFacts.hooks prepared base.vtable }

end Miri.Input.CompilerVirtualFacts
