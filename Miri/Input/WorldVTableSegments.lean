import Miri.Input.WorldDynMethods
import Miri.Input.VTableSegments

/-! On-demand source supertrait traversal in the execution's type universe.
This computes segments, not method instances, ABI shims or vtable allocations.
The no-trait-vptr session option is explicit; there is no implicit false policy. -/
namespace Miri.Input.WorldVTableSegments
open GenericSubstitution TraitSelection

private def sourceTrait (context : AliasRuntime.Context) (reference : TraitRef) :
    Except String TraitDeclaration := do
  let sources := context.traits.traits.filter (·.definition == reference.definition)
  unless sources.size == 1 do throw "vtable source trait absent or ambiguous"
  let some source := sources[0]? | throw "vtable source trait absent"
  unless source.parameters.size == reference.arguments.size do throw "vtable trait source arity mismatch"
  for (sort,argument) in source.parameters.zip reference.arguments do
    unless sort == argument.sort do throw "vtable trait source argument sort mismatch"
  pure source

private def normalize (context : AliasRuntime.Context) (work fuel : Nat) (reference : TraitRef) :
    Except String TraitRef := do
  let _ ← sourceTrait context reference
  let mut arguments := #[]
  for argument in reference.arguments do
    HigherRankedMatch.requireScoped 0 fuel argument
    let erased ← BinderRegions.eraseAndAnonymize fuel argument
    arguments := arguments.push (← AliasRuntime.normalizeTerm context work fuel #[] #[] erased)
  pure {reference with arguments := arguments}

def directSupertraits (context : AliasRuntime.Context) (work fuel : Nat) (reference : TraitRef) :
    Except String (Array TraitRef) := do
  let source ← sourceTrait context reference
  for argument in reference.arguments do
    HigherRankedMatch.requireScoped 0 fuel argument
    HigherRankedMatch.requireNormalized fuel argument
  for raw in source.superPredicates do
    HigherRankedMatch.validateSourceClause source.parameters fuel raw
  let clauses ← Substitution.clauses fuel reference.arguments source.superPredicates
  let mut result := #[]
  for clause in clauses do
    let .trait goal := clause.predicate | continue
    unless BinderRegions.regionOnly clause.variables do
      throw "vtable supertrait type or const binder requires its higher-ranked source provider"
    HigherRankedMatch.validateClause 0 fuel true clause
    let opened ← Universes.openClause (Universes.enter 0) fuel clause
    let .trait openedGoal := opened.predicate | throw "vtable opened supertrait predicate disappeared"
    let mut arguments := #[]
    for argument in openedGoal.traitRef.arguments do
      let erased ← BinderRegions.eraseAndAnonymize fuel argument
      arguments := arguments.push (← AliasRuntime.normalizeTerm context work fuel #[] #[] erased)
    result := result.push {goal.traitRef with arguments := arguments}
  pure result

/-- Query segments from ordered raw superclauses and source-derived method
eligibility. Distinct generic arguments remain distinct visited identities. -/
def prepare (context : AliasRuntime.Context) (work fuel : Nat) (noTraitVptr : Bool) (reference : TraitRef) :
    Except String (Array (VTableSegments.Segment TraitRef)) := do
  let reference ← normalize context work fuel reference
  let providers : VTableSegments.Providers TraitRef := {
    directSupertraits := directSupertraits context work fuel
    hasOwnEntries := fun reference => do
      pure !(← WorldDynMethods.ownMethods context work fuel reference.definition).isEmpty}
  VTableSegments.prepare providers fuel noTraitVptr reference

/-- The caller supplies its exact source no-trait-vptr policy. Method-instance
resolution and vtable allocation material remain separate runtime dependencies. -/
def query (work fuel : Nat) (noTraitVptr : Bool) (reference : TraitRef) :
    RuntimeArrayTypes.CompilerM (Array (VTableSegments.Segment TraitRef)) := do
  let world ← get
  match prepare world.metadata.normalizationContext work fuel noTraitVptr reference with
  | .ok value => pure value
  | .error error => throw error

end Miri.Input.WorldVTableSegments
