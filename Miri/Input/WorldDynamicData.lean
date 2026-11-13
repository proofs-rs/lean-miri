import Miri.Input.RuntimeArrayTypes
import Miri.Input.TypeArenaPredicateWorld
import Miri.Input.TraitSelection.Universes
import Miri.Interpreter.VirtualCalls

/-! Typed Dynamic data read from one execution World. This transports source
syntax; it does not establish dyn compatibility, candidate confirmation,
vtable predicate equality, allocation, MIR bodies or ABI. -/
namespace Miri.Input.WorldDynamicData
open Miri.Interpreter GenericSubstitution TraitSelection

structure View where
  private mk ::
  owner : Miri.MIR.TyId
  value : DynamicPredicate.Dynamic
  principal : Option DynamicPredicate.Predicate
  source : Term
  deriving Repr, DecidableEq

private def lift (result : Except String α) : RuntimeArrayTypes.CompilerM α :=
  match result with | .ok value => pure value | .error error => throw error

/-- Material predicate IDs are decoded ONLY through the current World's raw
source pool. Constructed embedded arrays are read as-is. No synthetic index. -/
def ofWorld (fuel : Nat) (world : TypeArena.World) (owner : Miri.MIR.TyId) : Except String (Option View) := do
  let (constructor,material) ← match ← world.lookupType owner with
    | .constructed constructor => pure (some constructor,false)
    | .material source => pure (← world.materialKey source,true)
  let some (.dynamic value) := constructor | return none
  let mut principal := none
  for predicate in value.predicates do
    unless BinderRegions.regionOnly predicate.variables do
      throw "typed dynamic runtime bridge: non-region existential binder unsupported"
    world.validateExistential predicate
    let _ ← world.definitionRef predicate.body.definition
    for id in predicate.body.typeChildren do let _ ← world.lookupType id; pure ()
    for id in predicate.body.constantChildren do let _ ← world.lookupConstant id; pure ()
    if let .trait .. := predicate.body then
      unless principal.isNone do throw "typed dynamic runtime bridge: multiple principals"
      principal := some predicate
  let source ← GenericInstantiationWorld.ofType world fuel owner
  -- Raw material types can refer to their surrounding source signature binder.
  -- Their immutable predicate handles retain that context; constructed owners
  -- must instead supply a closed standalone source term.
  unless material do BinderRegions.validateClosed #[] fuel source
  pure (some ⟨owner,value,principal,source⟩)

private def argumentSort : Miri.MIR.GenericArg → ArgSort
  | .Type _ => .type | .Lifetime _ => .region | .Const _ => .constant

private def checkArguments (parameters : Array ArgSort) (arguments : Array Miri.MIR.GenericArg) :
    Except String Unit := do
  unless parameters.size == arguments.size do throw "dynamic predicate source argument count mismatch"
  for (sort,argument) in parameters.zip arguments do
    unless sort == argumentSort argument do throw "dynamic predicate source argument sort mismatch"

private def traitSource (world : RuntimeArrayTypes.World) (definition : DefinitionIdentity) :
    Except String TraitDeclaration := do
  let context := world.metadata.normalizationContext
  let sources := context.traits.traits.filter (·.definition == definition)
  unless sources.size == 1 do throw "dynamic predicate trait source missing or ambiguous"
  let some source := sources[0]? | throw "dynamic predicate trait source absent"
  let scope ← SourceEnvironmentRuntime.lookupDefinitions context.generic.definitions definition
  unless scope.isTrait && scope.parameters == source.parameters &&
      scope.parameters[0]? == some .type && scope.parent == scope.genericParent do
    throw "dynamic predicate canonical trait source header mismatch"
  unless !source.isAlias do throw "dynamic predicate trait alias requires its source provider"
  pure source

/-- Transport does not prove dyn compatibility or object candidate selection.
It does require the declaration kinds and complete argument headers to agree. -/
private def validateSource (world : RuntimeArrayTypes.World) (view : View) : Except String Unit := do
  for predicate in view.value.predicates do
    match predicate.body with
    | .trait definition arguments =>
      let source ← traitSource world definition
      unless !source.isAuto do throw "dynamic principal source is an auto trait"
      checkArguments (source.parameters.extract 1 source.parameters.size) arguments
    | .autoTrait definition =>
      let source ← traitSource world definition
      unless source.isAuto && source.parameters.size == 1 do
        throw "dynamic auto-trait predicate source header mismatch"
    | .projection definition arguments term =>
      let context := world.metadata.normalizationContext
      let members := context.traits.traits.flatMap fun source => source.members.filterMap fun member =>
        if member.definition == definition then some (source,member) else none
      unless members.size == 1 do throw "dynamic projection source missing or ambiguous"
      let some (owner,member) := members[0]? | throw "dynamic projection source absent"
      let _ ← traitSource world owner.definition
      let expected := match term with | .type _ => "type" | .constant _ => "constant"
      unless member.kind == expected do throw "dynamic projection term kind disagrees with source declaration"
      unless !member.isImplTraitInTrait do throw "dynamic RPITIT projection requires its source provider"
      let scope ← SourceEnvironmentRuntime.lookupDefinitions context.generic.definitions definition
      let some parent := scope.genericParent | throw "dynamic projection generic parent absent"
      unless scope.parent == scope.genericParent && parent.definition == owner.definition &&
          parent.parameterCount == owner.parameters.size &&
          scope.parameters.take parent.parameterCount == owner.parameters do
        throw "dynamic projection canonical source header mismatch"
      checkArguments (scope.parameters.extract 1 scope.parameters.size) arguments

def query (fuel : Nat) (owner : Miri.MIR.TyId) : RuntimeArrayTypes.CompilerM (Option View) := do
  let world ← get
  let result ← lift (ofWorld fuel world.arena owner)
  if let some view := result then lift (validateSource world view)
  pure result

/-- A consumer rereads the owner in the current execution World. The payload is
an ephemeral view, never a transferable compiler-session/global token. -/
def validate (fuel : Nat) (view : View) : RuntimeArrayTypes.CompilerM Unit := do
  unless (← query fuel view.owner) == some view do
    throw "typed dynamic runtime bridge: owner/payload differs from current World"

/-- Exact outer region-binder opening, then erasure for the first-slot query.
Nested binders retain their own variables; type/const binders reject above. -/
def principalRef (fuel : Nat) (view : View) : RuntimeArrayTypes.CompilerM TraitRef := do
  validate fuel view
  let some predicate := view.principal | throw "object method candidate requires a principal"
  let .trait definition arguments := predicate.body | throw "principal is not a trait"
  let world ← get
  let selfTerm ← lift (GenericInstantiationWorld.ofType world.arena fuel view.owner)
  let arguments ← lift (GenericInstantiationWorld.ofArguments world.arena fuel arguments)
  let arguments ← lift (arguments.mapM fun term => do
    let opened ← Universes.openTerm predicate.variables 1 fuel 0 term
    BinderRegions.eraseAndAnonymize fuel opened)
  pure ⟨definition,#[selfTerm] ++ arguments⟩

/-- Physical trait definition conversion is distinct from the legacy runtime
principal, which is a predicate handle rather than a DefinitionRef. -/
def principalDefinition (fuel : Nat) (view : View) :
    RuntimeArrayTypes.CompilerM (Option DefinitionRef) := do
  validate fuel view
  let some predicate := view.principal | return none
  let .trait definition _ := predicate.body | throw "dynamic principal is not a trait"
  some <$> lift ((← get).arena.definitionRef definition)

/-- Material predicate IDs remain unchanged. Constructed predicates receive
real checked handles in this execution World's append-only predicate arena. -/
def runtimeData (fuel : Nat) (owner : Miri.MIR.TyId) :
    RuntimeArrayTypes.CompilerM (Option VirtualCalls.DynamicData) := do
  let world ← get
  match ← lift (world.arena.lookupType owner) with
  | .material node =>
    match node.shape with
    | .dynamicTraitObject predicates principal _ => return some ⟨predicates,principal⟩
    | _ => return none
  | .constructed (.dynamic _) =>
    let some view ← query fuel owner | throw "dynamic owner source shape changed"
    let mut predicates := #[]
    let mut principal := none
    for predicate in view.value.predicates do
      let handle ← RuntimeArrayTypes.liftType (TypeArena.World.internExistential predicate fuel)
      predicates := predicates.push handle
      if let .trait .. := predicate.body then principal := some handle
    return some ⟨predicates,principal⟩
  | .constructed _ => return none

/-- Unported result-catalog leaves may consume only their real immutable
prefix. A valid suffix handle must never be dropped or reinterpreted as a row. -/
def requireMaterialPredicates (values : PredicateList) : RuntimeArrayTypes.CompilerM Unit := do
  let world ← get
  for id in values do
    let _ ← lift (world.arena.existential id)
    unless id < world.arena.materialPredicates.size do
      throw "constructed runtime predicate requires source vtable comparison/normalization/allocation"

def requireMaterialPrincipal (principal : Option Nat) : RuntimeArrayTypes.CompilerM Unit := do
  let some id := principal | return ()
  requireMaterialPredicates #[id]
  let predicate ← lift ((← get).arena.existential id)
  let .trait .. := predicate.body | throw "vtable principal predicate is not a trait"

def requireMaterialType (id : Miri.MIR.TyId) : RuntimeArrayTypes.CompilerM Unit := do
  let .material _ ← lift ((← get).arena.lookupType id)
    | throw "constructed type requires source vtable query"
  pure ()

end Miri.Input.WorldDynamicData
