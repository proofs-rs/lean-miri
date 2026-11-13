import Miri.Input.WorldDynamicData
import Miri.Input.AliasRuntime
import Miri.Input.DynMethodEligibility

/-! Narrow pinned ground auto-trait selection for Dynamic Self. Dynamic types
receive no structural AutoImplCandidate. Explicit auto bounds are builtin object
witnesses; positive principal supertraits can supply an ObjectCandidate.
A negative answer requires a complete raw manual-impl catalog with no possibly
matching head, not merely absence of an existential auto bound. -/
namespace Miri.Input.WorldDynamicAutoTrait
open GenericSubstitution TraitSelection
private def lift (result : Except String α) : RuntimeArrayTypes.CompilerM α :=
  match result with | .ok value => pure value | .error e => throw e

/-- Every existing RelevantImpl.Key is disjoint from rustc's Trait/MarkerTraitObject
keys. A source head simplifying to none is a potentially matching blanket impl.
A dynamic or otherwise unsupported source head errors rather than being dropped. -/
private def manualPossible (fuel : Nat) (implementation : Impl) : Except String Bool := do
  let some source := implementation.traitRef.arguments[0]? | throw "dyn auto impl Self absent"
  RelevantImpl.dynamicHeadPossible fuel source

private def sourceTrait (context : AliasRuntime.Context) (identity : DefinitionIdentity) :
    Except String TraitDeclaration := do
  let rows := context.traits.traits.filter (·.definition == identity)
  unless rows.size == 1 do throw "dyn auto trait source missing or ambiguous"
  let some source := rows[0]? | throw "dyn auto trait source absent"
  pure source

def query (fuel : Nat) (id : TypeId) (declaration : TraitDeclaration) :
    RuntimeArrayTypes.CompilerM (Option Bool) := do
  let some view ← WorldDynamicData.query fuel id | return none
  let world ← get
  let context := world.metadata.normalizationContext
  unless declaration.isAuto && !declaration.isAlias && declaration.parameters == #[.type] do
    throw "dyn auto query requires a canonical auto-trait declaration"
  unless declaration.members.isEmpty do throw "dyn auto source trait declares associated members"
  let mut seen := #[]
  for implementation in declaration.implementations do
    unless implementation.traitRef.definition == declaration.definition do
      throw "dyn auto impl belongs to another trait source"
    if seen.contains implementation.definition then throw "dyn auto duplicate raw impl definition"
    seen := seen.push implementation.definition
    if ← lift (manualPossible fuel implementation) then
      throw "dyn auto possibly applicable manual impl requires source candidate winnowing"
  for predicate in view.value.predicates do
    if let .autoTrait identity := predicate.body then
      if identity == declaration.definition then
        unless predicate.variables.isEmpty do throw "dyn auto bound cannot bind variables"
        return some true
  let some predicate := view.principal | return some false
  unless predicate.variables.isEmpty do throw "dyn auto principal higher-ranked relation requires universe provider"
  let principal ← WorldDynamicData.principalRef fuel view
  let assumptions : Array Clause := #[⟨#[],.trait ⟨.positive,principal⟩⟩]
  let goal : TraitRef := ⟨declaration.definition,#[view.source]⟩
  -- Absence becomes a negative only after a complete ground supertrait walk.
  -- EnvironmentEntailment alone can return none for unsupported bound clauses.
  let mut queue := #[principal]
  let mut visited : Array TraitRef := #[]
  let mut cursor := 0
  for _ in [:fuel] do
    let some reference := queue[cursor]? | break
    cursor := cursor+1
    if visited.contains reference then continue
    visited := visited.push reference
    let source ← lift (sourceTrait context reference.definition)
    unless source.parameters.size == reference.arguments.size do throw "dyn auto source supertrait arity mismatch"
    for (sort,argument) in source.parameters.zip reference.arguments do
      unless sort == argument.sort do throw "dyn auto source supertrait argument sort mismatch"
      lift (Match.requireGround fuel argument)
    for raw in source.superPredicates do
      lift (HigherRankedMatch.validateSourceClause source.parameters fuel raw)
    let supers ← lift (Substitution.clauses fuel reference.arguments source.superPredicates)
    for clause in supers do
      unless clause.variables.isEmpty do throw "dyn auto supertrait higher-ranked relation requires universe provider"
      let .trait superGoal := clause.predicate | throw "dyn auto source superpredicate requires confirmation provider"
      unless superGoal.polarity == .positive && superGoal.traitRef.arguments[0]? == some view.source do
        throw "dyn auto supertrait must retain positive canonical Self"
      queue := queue.push superGoal.traitRef
  unless cursor == queue.size do throw "dyn auto supertrait traversal exhausted"
  let proof ← lift (EnvironmentEntailment.entails context.traits #[] assumptions fuel ⟨#[],.trait ⟨.positive,goal⟩⟩)
  if proof.isNone then
    if visited.contains goal then throw "dyn auto source witness unexpectedly absent"
    return some false
  -- This candidate targets an auto trait, so it has no callable/associated type
  -- members to confirm. Nested explicit positive supertraits must be implied
  -- by the same checked object witness; unsupported categories never disappear.
  for raw in declaration.superPredicates do
    lift (HigherRankedMatch.validateSourceClause declaration.parameters fuel raw)
  let nested ← lift (Substitution.clauses fuel goal.arguments declaration.superPredicates)
  for clause in nested do
    unless clause.variables.isEmpty do throw "dyn auto nested higher-ranked relation requires universe provider"
    let .trait nestedGoal := clause.predicate | throw "dyn auto nested predicate requires source confirmation"
    unless nestedGoal.polarity == .positive do throw "dyn auto nested negative trait requires source confirmation"
    let nestedSource ← lift (sourceTrait context nestedGoal.traitRef.definition)
    unless nestedSource.builtin == some .metaSized || nestedSource.isAuto do
      throw "dyn auto nested nonauto trait requires source confirmation"
    let witness ← lift (EnvironmentEntailment.entails context.traits #[] assumptions fuel clause)
    unless witness.isSome do throw "dyn auto nested object obligation was not established"
  pure (some true)
end Miri.Input.WorldDynamicAutoTrait
