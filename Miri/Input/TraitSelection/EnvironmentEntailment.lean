import Miri.Input.TraitSelection.Substitution
import Miri.Input.TraitSelection.Codec

/-! Positive source-environment consequence closure in one declaration's
validated early-parameter scope. `none` means not proved by this fragment,
NEVER a negative Sized or trait answer. No impl selection or inference occurs. -/
namespace Miri.Input.TraitSelection.EnvironmentEntailment
open GenericSubstitution
inductive Derivation where
  | assumption (index : Nat)
  | superClause (parent : Derivation) (traitDefinition : DefinitionIdentity) (index : Nat)
  deriving Repr

private def declaration (program : Program) (identity : DefinitionIdentity) : Except String TraitDeclaration := do
  let matching := program.traits.filter (·.definition == identity)
  unless matching.size == 1 do throw "source environment trait declaration missing or ambiguous"
  let some source := matching[0]? | throw "source environment trait declaration absent"
  pure source

private def visit (program : Program) (goal : Clause) (termFuel : Nat) :
    Nat → Array (Clause × Derivation) → Array Clause → Nat → Except String (Option Derivation)
  | 0, queue, _, cursor =>
    if cursor >= queue.size then pure none else throw "source environment consequence work exhausted"
  | work + 1, queue, seen, cursor => do
    let some (clause, proof) := queue[cursor]? | return none
    if clause = goal then return some proof
    if !clause.variables.isEmpty then return (← visit program goal termFuel work queue seen (cursor + 1))
    let mut queue := queue
    let mut seen := seen
    match clause.predicate with
    | .trait ⟨.positive, reference⟩ =>
      let source ← declaration program reference.definition
      unless source.parameters.size == reference.arguments.size do
        throw "source environment supertrait argument arity mismatch"
      for (parameter, argument) in source.parameters.zip reference.arguments do
        unless parameter == argument.sort do throw "source environment supertrait argument sort mismatch"
      let supers ← Substitution.clauses termFuel reference.arguments source.superPredicates
      for index in [:supers.size] do
        let some consequence := supers[index]? | throw "source environment superclause index absent"
        if seen.any (fun prior => decide (prior = consequence)) then continue
        seen := seen.push consequence
        queue := queue.push (consequence,.superClause proof source.definition index)
    | _ => pure ()
    visit program goal termFuel work queue seen (cursor + 1)

def entails (program : Program) (parameters : Array ArgSort) (assumptions : Array Clause)
    (work : Nat) (goal : Clause) : Except String (Option Derivation) := do
  unless goal.variables.isEmpty do throw "higher-ranked environment entailment requires binder relations"
  Codec.validateClauses parameters assumptions
  Codec.validateClauses parameters #[goal]
  let queue := assumptions.mapIdx fun index clause => (clause,Derivation.assumption index)
  visit program goal (work + 1) work queue assumptions 0

end Miri.Input.TraitSelection.EnvironmentEntailment
