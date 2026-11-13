import Miri.Input.AliasRuntime
import Miri.Input.TypeArenaPredicateWorld
import Miri.Input.TraitSelection.Universes

/-! Checked Dynamic syntax and raw source headers, independent of runtime wrappers. -/
namespace Miri.Input.SourceDynamicView
open GenericSubstitution TraitSelection

structure View where
  private mk ::
  owner : Miri.MIR.TyId
  value : DynamicPredicate.Dynamic
  principal : Option DynamicPredicate.Predicate
  source : Term
  deriving Repr, DecidableEq

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

private def traitSource (context : AliasRuntime.Context) (definition : DefinitionIdentity) :
    Except String TraitDeclaration := do
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
private def validateSource (context : AliasRuntime.Context) (view : View) : Except String Unit := do
  for predicate in view.value.predicates do
    match predicate.body with
    | .trait definition arguments =>
      let source ← traitSource context definition
      unless !source.isAuto do throw "dynamic principal source is an auto trait"
      checkArguments (source.parameters.extract 1 source.parameters.size) arguments
    | .autoTrait definition =>
      let source ← traitSource context definition
      unless source.isAuto && source.parameters.size == 1 do
        throw "dynamic auto-trait predicate source header mismatch"
    | .projection definition arguments term =>
      let members := context.traits.traits.flatMap fun source => source.members.filterMap fun member =>
        if member.definition == definition then some (source,member) else none
      unless members.size == 1 do throw "dynamic projection source missing or ambiguous"
      let some (owner,member) := members[0]? | throw "dynamic projection source absent"
      let _ ← traitSource context owner.definition
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

def query (context : AliasRuntime.Context) (fuel : Nat) (world : TypeArena.World)
    (owner : Miri.MIR.TyId) : Except String (Option View) := do
  let result ← ofWorld fuel world owner
  if let some view := result then validateSource context view
  pure result

end Miri.Input.SourceDynamicView
