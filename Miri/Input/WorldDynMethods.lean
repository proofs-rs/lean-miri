import Miri.Input.RuntimeArrayTypes
import Miri.Input.DynMethodEligibility

/-! Source-defined own-method eligibility for vtable segments. This reads the
current execution's immutable raw declarations, not compiler own-entry rows.
Unknown receiver or constant semantics remain errors, never omitted entries. -/
namespace Miri.Input.WorldDynMethods
open GenericSubstitution TraitSelection

private def sourceScope (context : AliasRuntime.Context) : SourceEnvironment.Lookup := fun identity => do
  let scope ← SourceEnvironmentRuntime.lookupDefinitions context.generic.definitions identity
  for clause in scope.ownPredicates do
    HigherRankedMatch.validateSourceClause scope.parameters 16384 clause
  pure scope

private def definition (context : AliasRuntime.Context) (identity : DefinitionIdentity) :
    Except String DefinitionId := do
  let reference ← GenericInstantiation.definitionRef context.generic identity
  let some source := context.generic.definitions[reference]? | throw "dyn source definition absent"
  pure source

private def traitSource (context : AliasRuntime.Context) (identity : DefinitionIdentity) :
    Except String TraitDeclaration := do
  let sources := context.traits.traits.filter (·.definition == identity)
  unless sources.size == 1 do throw "dyn source trait missing or ambiguous"
  let some source := sources[0]? | throw "dyn source trait absent"
  pure source

private def projection (context : AliasRuntime.Context) (identity : DefinitionIdentity) :
    Except String DynMethodEligibility.Projection := do
  let mut result : Option DynMethodEligibility.Projection := none
  for source in context.traits.traits do
    for member in source.members do
      if member.definition != identity then continue
      unless result.isNone do throw "dyn projection source member duplicated"
      unless member.kind == "type" || member.kind == "constant" do
        throw "dyn projection source member is not a type or constant"
      result := some ⟨source.definition,source.parameters.size,member.isImplTraitInTrait⟩
  let some resolved := result | throw "dyn projection source member absent"
  pure resolved

private def method (context : AliasRuntime.Context) (traitDeclaration : TraitDeclaration)
    (member : TraitMember) (fuel : Nat) : Except String DynMethodEligibility.Method := do
  unless member.kind == "function" do throw "dyn method requested for a nonfunction source member"
  let source ← definition context member.definition
  let scope ← sourceScope context member.definition
  let some parent := scope.genericParent | throw "dyn method source generic parent absent"
  unless scope.parent == scope.genericParent && parent.definition == traitDeclaration.definition &&
      parent.parameterCount == traitDeclaration.parameters.size do
    throw "dyn method source generic and predicate parent mismatch"
  let some template := source.genericTemplate | throw "dyn method source signature template absent"
  unless template.parameters == scope.parameters && template.fields.isEmpty do
    throw "dyn method source template header differs from canonical scope"
  let .definition .type "function_definition" identity _ := template.typeExpression
    | throw "dyn method template is not a source function definition"
  unless identity == member.definition do throw "dyn method template physical identity mismatch"
  let some signature := template.signatureExpression | throw "dyn method raw function signature absent"
  let inherited ← SourceEnvironment.predicates (sourceScope context) fuel parent.definition
  pure {
    definition := member.definition,traitDefinition := traitDeclaration.definition,
    parameters := scope.parameters,parentParameterCount := parent.parameterCount,
    isMethod := member.isMethod,isFinal := member.isFinal,signature := signature,
    ownClauses := scope.ownPredicates,inheritedClauses := inherited}

private def predicateTerms : Predicate → Array Term
  | .trait goal => goal.traitRef.arguments
  | .hostEffect _ reference => reference.arguments
  | .equal left right | .regionOutlives left right | .typeOutlives left right
  | .constHasType left right => #[left,right]
  | .projection _ _ arguments expected => arguments.push expected
  | .constEvaluatable value | .wellFormed value => #[value]
  | .unstableFeature _ => #[]

private def receiver (context : AliasRuntime.Context) (work fuel : Nat)
    (query : DynMethodEligibility.ReceiverQuery) : Except String Bool := do
  -- All source parameters become rigid universals before impl inference starts.
  -- The appended U has a distinct index in this exact declaration header.
  let arguments := query.parameters.mapIdx fun index sort => Term.placeholder sort 1 index .anonymous
  let assumptions ← Substitution.clauses fuel arguments query.assumptions
  for clause in assumptions do
    for term in predicateTerms clause.predicate do HigherRankedMatch.requireNormalized fuel term
  let goalArguments ← query.goal.traitRef.arguments.mapM (GenericSubstitution.instantiate fuel arguments)
  let goal := {query.goal with traitRef := {query.goal.traitRef with arguments := goalArguments}}
  let normalize := fun universeIndex remaining (_active : Array Goal) term =>
    ScopedNormalization.normalize universeIndex remaining term
  let base := AliasRuntime.traitHooks context fuel normalize
  let hooks : Hooks := {base with
    implementationPredicates := fun implementation =>
      SourceEnvironment.predicates (sourceScope context) fuel implementation.definition
    -- candidate_assembly.rs has no builtin DispatchFromDyn candidate. Its raw
    -- ordinary implementations and mandatory own clauses decide the relation.
    builtin := fun universeIndex remaining active source goal =>
      if source.langItem == some "dispatch_from_dyn" then pure none
      else base.builtin universeIndex remaining active source goal}
  match ← solveInUniverseWithActive context.traits hooks {assumptions := assumptions,eraseRegions := true}
      1 fuel work #[] goal with
  | .proven _ => pure true
  | .noSolution => pure false
  | .ambiguous reason => throw s!"dyn receiver obligation remains ambiguous: {reason}"

private def hooks (context : AliasRuntime.Context) (work fuel : Nat) : DynMethodEligibility.Hooks := {
  projection := projection context
  expandAbstractConst := fun term =>
    match term with
    | .parameter .constant .. | .placeholder .constant .. | .bound .constant .. => pure term
    | .node .constant "value" .. => pure term
    | _ => throw "dyn method abstract constant expansion requires its source CTFE provider"
  receiver := receiver context work fuel
  constProjections := none}

/-- Own methods in raw associated-item declaration order. No compiler vtable or
per-method eligibility answer is consumed. This does not resolve method shims. -/
def ownMethods (context : AliasRuntime.Context) (work fuel : Nat) (identity : DefinitionIdentity) :
    Except String (Array DefinitionIdentity) := do
  let source ← traitSource context identity
  let mut result := #[]
  for member in source.members do
    unless member.kind == "function" do continue
    if member.isFinal then continue
    let method ← method context source member fuel
    if ← DynMethodEligibility.ownEntry context.traits (hooks context work fuel) method fuel then
      result := result.push member.definition
  pure result

/-- Read declarations from the current execution-owned World. -/
def query (identity : DefinitionIdentity) (work fuel : Nat) : RuntimeArrayTypes.CompilerM (Array DefinitionIdentity) := do
  let world ← get
  match ownMethods world.metadata.normalizationContext work fuel identity with
  | .ok value => pure value
  | .error error => throw error

end Miri.Input.WorldDynMethods
