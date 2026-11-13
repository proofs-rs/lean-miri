import Miri.Input.WorldVTableMethods
import Miri.Input.CompilerRuntimeQueries

/-! Final vtable instance syntax for covered ordinary source implementations.
This is separate from MIR bodies, FnAbi and allocation. Dynamic object candidate
selection and closure dispatch require their source providers and remain errors. -/
namespace Miri.Input.WorldVTableInstance
open GenericSubstitution TraitSelection Miri.Interpreter

inductive Kind where
  | item | vtable | reify (reason : Option CallReifyReason)
  deriving Repr, DecidableEq

structure Declaration where
  kind : Kind
  definition : DefinitionIdentity
  arguments : Array Term
  deriving Repr, DecidableEq

private def source (context : AliasRuntime.Context) (identity : DefinitionIdentity) :
    Except String (DefinitionRef × DefinitionId × CallableSource) := do
  let reference ← GenericInstantiation.definitionRef context.generic identity
  let some definition := context.generic.definitions[reference]?
    | throw "vtable callable source definition absent"
  let some callable := definition.callableSource | throw "vtable raw callable header absent"
  unless callable.definitionKind == "associated_function" do
    throw "vtable closure or nonassociated callable requires its source dispatch provider"
  let some scope := definition.sourceEnvironment | throw "vtable callable source scope absent"
  unless scope.parent == scope.genericParent do throw "vtable callable generic and predicate parent disagree"
  let some parent := scope.genericParent | throw "vtable callable associated parent absent"
  let parentReference ← GenericInstantiation.definitionRef context.generic parent.definition
  let some parentDefinition := context.generic.definitions[parentReference]?
    | throw "vtable callable parent source absent"
  let some parentScope := parentDefinition.sourceEnvironment
    | throw "vtable callable parent scope absent"
  unless parent.parameterCount == parentScope.parameters.size &&
      scope.parameters.take parent.parameterCount == parentScope.parameters do
    throw "vtable callable parent generic header mismatch"
  if callable.container == some "trait" then
    unless parentScope.isTrait && callable.traitItem.isNone && callable.hasSelf do
      throw "vtable callable trait header inconsistent"
  else if callable.container == some "trait_impl" then
    unless !parentScope.isTrait && callable.traitItem.isSome do
      throw "vtable callable impl header inconsistent"
  else throw "vtable callable requires a trait or trait-impl container"
  pure (reference,definition,callable)

private def rawSignature (definition : DefinitionId) (identity : DefinitionIdentity) :
    Except String RawFunctionSignature.Signature := do
  let some template := definition.genericTemplate | throw "vtable callable raw template absent"
  let some scope := definition.sourceEnvironment | throw "vtable callable source scope absent"
  unless template.parameters == scope.parameters do throw "vtable callable template generic header mismatch"
  let .definition .type "function_definition" actual _ := template.typeExpression
    | throw "vtable callable source template is not a function definition"
  unless actual == identity do throw "vtable callable template physical identity mismatch"
  let some signature := template.signatureExpression | throw "vtable callable raw signature absent"
  RawFunctionSignature.read signature

private def caller (context : AliasRuntime.Context) (reference : DefinitionRef) : Except String Bool :=
  CompilerRuntimeQueries.instanceRequiresCallerLocation context.generic.definitions (.Item reference)

/-- Pinned codegen_attrs.rs::should_inherit_track_caller. For the covered
Fn/AssocFn declarations body_codegen_attrs and codegen_fn_attrs agree. -/
private def inheritsCaller (context : AliasRuntime.Context) (callable : CallableSource)
    (original : DefinitionIdentity) : Except String Bool := do
  let some prototype := callable.traitItem | return false
  unless prototype == original do throw "vtable callable selected impl maps to another trait method"
  let (reference,_,header) ← source context prototype
  unless header.container == some "trait" do throw "vtable callable prototype is not a trait method"
  caller context reference

private def reifyReason (kcfi : Option Bool) : Except String (Option CallReifyReason) := do
  let some enabled := kcfi | throw "vtable reification raw sanitizer policy absent"
  pure (if enabled then some .Vtable else none)

/-- Postprocess a source-selected ordinary declaration. `kcfi` must be derived
from raw session sanitizer material by the requesting World adapter. Its absence
is an error precisely when the covered branch constructs a Reify instance. -/
def finish (context : AliasRuntime.Context) (kcfi : Option Bool)
    (original : DefinitionIdentity) (slot : WorldVTableMethods.Slot) :
    Except String (Option Declaration) := do
  match slot with
  | .vacant => pure none
  | .byValueShim method =>
    unless method.definition == original do throw "vtable by-value shim changed its original method"
    let (_,definition,header) ← source context original
    let signature ← rawSignature definition original
    unless header.container == some "trait" && header.hasSelf &&
        signature.inputs[0]? == some (.parameter .type 0) do
      throw "vtable by-value shim raw receiver or Self header mismatch"
    pure (some ⟨.vtable,original,method.arguments⟩)
  | .selected method =>
    let (reference,definition,header) ← source context method.definition
    let _ ← rawSignature definition method.definition
    if header.container == some "trait" then
      unless method.definition == original do throw "vtable trait default changed its original method"
    else
      unless header.traitItem == some original do throw "vtable selected impl trait method mapping mismatch"
    let requiresCaller ← caller context reference
    let inherited ← inheritsCaller context header original
    let kind ← if requiresCaller && !inherited && header.container != some "trait" then
      pure (.reify (← reifyReason kcfi)) else pure .item
    pure (some ⟨kind,method.definition,method.arguments⟩)

/-- Component port of the Virtual postprocessing branch. This does not derive
an object candidate or a Virtual slot; callers must establish that separate
source selection before using it. Ordinary ownInstances does not call it. -/
def finishVirtual (context : AliasRuntime.Context) (kcfi : Option Bool)
    (method : DefinitionIdentity) (arguments : Array Term) : Except String Declaration := do
  let (_,definition,header) ← source context method
  unless header.container == some "trait" do throw "vtable Virtual method is not a trait declaration"
  let signature ← rawSignature definition method
  if header.hasSelf && signature.inputs[0]? == some (.parameter .type 0) then
    throw "vtable by-value receiver precedes Virtual resolution"
  pure ⟨.reify (← reifyReason kcfi),method,arguments⟩

def ownDeclarations (context : AliasRuntime.Context) (work fuel : Nat) (kcfi : Option Bool)
    (reference : TraitRef) : Except String (Array (Option Declaration)) := do
  let identities ← WorldDynMethods.ownMethods context work fuel reference.definition
  let slots ← WorldVTableMethods.ownSlots context work fuel reference
  unless identities.size == slots.size do throw "vtable own source methods and concrete slots disagree"
  (identities.zip slots).mapM fun (identity,slot) => finish context kcfi identity slot

private def lift (result : Except String α) : RuntimeArrayTypes.CompilerM α :=
  match result with | .ok value => pure value | .error error => throw error

/-- Construct only canonical syntax in the current World. Body, ABI and
function allocation providers must establish their own separate capabilities. -/
def intern (fuel : Nat) (declaration : Declaration) : RuntimeArrayTypes.CompilerM InstanceId := do
  let definition ← lift ((← get).arena.definitionRef declaration.definition)
  let arguments ← RuntimeArrayTypes.liftType
    (GenericInstantiationWorld.resolveArguments fuel declaration.arguments)
  let kind := match declaration.kind with
    | .item => CallInstanceKind.Item definition
    | .vtable => .Shim (.VTable definition)
    | .reify reason => .Shim (.Reify definition reason)
  RuntimeArrayTypes.internInstance kind arguments

/-- Derive KCFI from the current World's raw sanitizer set. Dynamic Self requires
the still-unimplemented object candidate provider; no Virtual instance is guessed. -/
def ownInstances (work fuel : Nat) (reference : TraitRef) :
    RuntimeArrayTypes.CompilerM (Array (Option InstanceId)) := do
  let world ← get
  let kcfi := world.metadata.source.producer.abiSession.map (fun session => session.sanitizers.contains "kcfi")
  let declarations ← lift (ownDeclarations world.metadata.normalizationContext work fuel kcfi reference)
  declarations.mapM fun value => match value with
    | none => pure none
    | some declaration => some <$> intern fuel declaration

end Miri.Input.WorldVTableInstance
