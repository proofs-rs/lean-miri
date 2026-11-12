import Miri.Input.TraitSelection.Match
import Miri.Input.TraitSelection.Substitution
import Miri.Input.TraitSelection.RelevantImpl
import Miri.Input.TraitSelection.StructuralCycle
import Miri.Input.TraitSelection.EnvironmentEntailment

/-! Selection and nested-obligation fulfillment over complete raw impl catalogs.
Pinned rustc candidate assembly/confirmation first relates an impl head, then
instantiates and fulfills its predicates. This module retains that distinction;
a matching head alone is not proof. Negative impls, failed where clauses,
default impls, overlapping candidates, cycles and missing catalogs
cannot become a guessed successful selection.

The initial executable relation is for ground, uniquely selected ordinary
impls. Higher-ranked universe relations, specialization ordering and builtin
trait assembly require explicit semantic providers; they are not replaced by
syntactic success. Depth and total query work are separately bounded. The ground unique structural-auto fragment admits certified rational
backedges; other cycles remain ambiguous. No shared or provisional result cache
is used. -/
namespace Miri.Input.TraitSelection
open GenericSubstitution

inductive Evidence where
  | assumption (index : Nat)
  | implementation (selection : ImplSelection) (obligations : Array Evidence)
  | builtin (goal : Goal) (obligations : Array Evidence)
  | sourceEnvironment (derivation : EnvironmentEntailment.Derivation)
  | structuralBackedge (goal : Goal) (start : Nat)
  | equality (value : Term)
  | regionErasure
  | conjunction (obligations : Array Evidence)
  deriving Repr

inductive Outcome where
  | proven (evidence : Evidence)
  | noSolution
  | ambiguous (reason : String)
  deriving Repr

structure Hooks where
  /-- Normalize actual generic trees using raw alias/impl declarations. -/
  normalize : Nat → Array Goal → Term → Except String Term
  /-- Return source-derived nested obligations for a real builtin candidate.
  An unimplemented builtin must error, not claim that no candidate exists. -/
  builtin : Nat → Array Goal → TraitDeclaration → Goal → Except String (Option (Array Clause))
  /-- Remaining predicate categories require a real implementation. -/
  external : Nat → Array Goal → Environment → Predicate → Except String Outcome

private abbrev Engine := StateT Nat (Except String)

private def step : Engine Unit := do
  let remaining ← get
  if remaining == 0 then throw "trait fulfillment total work exhausted"
  set (remaining - 1)

private def declaration (program : Program) (definition : DefinitionIdentity) :
    Except String TraitDeclaration := do
  let matching := program.traits.filter (·.definition == definition)
  unless matching.size == 1 do throw "raw trait declaration catalog missing or ambiguous"
  let some value := matching[0]? | throw "raw trait declaration absent"
  if value.isAlias && !value.implementations.isEmpty then
    throw "trait alias cannot declare impl candidates"
  let mut seen : Array DefinitionIdentity := #[]
  for implementation in value.implementations do
    unless implementation.traitRef.definition == definition do throw "impl belongs to another trait catalog"
    if seen.contains implementation.definition then throw "duplicate raw impl definition"
    seen := seen.push implementation.definition
  pure value

private def normalizedGoal (hooks : Hooks) (fuel : Nat) (active : Array Goal) (goal : Goal) :
    Except String Goal := do
  let arguments ← goal.traitRef.arguments.mapM fun arg => do
    let result ← hooks.normalize fuel active arg
    Match.requireGround fuel result
    pure result
  pure {goal with traitRef := {goal.traitRef with arguments}}

private def collect (values : Array Outcome) : Outcome := Id.run do
  let mut proofs := #[]
  let mut ambiguity : Option String := none
  for result in values do
    match result with
    | .noSolution => return .noSolution
    | .ambiguous reason => ambiguity := some reason
    | .proven proof => proofs := proofs.push proof
  if let some reason := ambiguity then return .ambiguous reason
  return .proven (.conjunction proofs)

mutual
private def solveCore (program : Program) (hooks : Hooks) (environment : Environment) (entryBoundary : Nat) :
    Nat → Array Goal → Goal → Engine Outcome
  | 0, _, _ => throw "trait selection recursion exhausted"
  | fuel + 1, active, original => do
    step
    let goal ← liftM (normalizedGoal hooks (fuel + 1) active original)
    if let some allowed := program.constructorScope then
      for argument in goal.traitRef.arguments do
        liftM (Match.requireConstructorScope allowed (fuel + 1) argument)
    let source ← liftM (declaration program goal.traitRef.definition)
    unless source.parameters.size == goal.traitRef.arguments.size do throw "trait query argument arity mismatch"
    for (parameter, argument) in source.parameters.zip goal.traitRef.arguments do
      unless parameter == argument.sort do throw "trait query argument sort mismatch"
    let some self := goal.traitRef.arguments[0]? | throw "trait query Self absent"
    if let .node .type "dynamic" _ _ := self then
      unless source.builtin == some .sized || source.builtin == some .metaSized do
        throw "dynamic trait goals require object candidate assembly"
    if goal.polarity == .positive && !environment.assumptions.isEmpty then
      let proof ← liftM (EnvironmentEntailment.entails program #[] environment.assumptions (fuel + 1)
        ⟨#[],.trait goal⟩)
      if let some proof := proof then return .proven (.sourceEnvironment proof)
    if active.any (fun prior => decide (prior = goal)) then
      if let some start ← liftM (StructuralCycle.certify program environment (fuel + 1) active goal entryBoundary) then
        return .proven (.structuralBackedge goal start)
      return .ambiguous "trait cycle requires coinductive universe-aware evaluation"
    let active := active.push goal
    for index in [:environment.assumptions.size] do
      let some clause := environment.assumptions[index]? | throw "environment clause index absent"
      if let .trait assumed := clause.predicate then
        if assumed.traitRef.definition == goal.traitRef.definition then
          unless clause.variables.isEmpty do throw "higher-ranked environment requires universe instantiation"
          let assumed ← liftM (normalizedGoal hooks fuel active assumed)
          if assumed = goal then return .proven (.assumption index)
    if source.isAlias then
      unless goal.polarity == .positive do throw "negative trait-alias evaluation is not implemented"
      let predicates ← liftM (Substitution.clauses fuel goal.traitRef.arguments source.superPredicates)
      let mut results := #[]
      for predicate in predicates do
        results := results.push (← fulfillCore program hooks environment entryBoundary fuel active predicate)
      return collect results
    let mut candidates : Array Evidence := #[]
    let mut opposite := false
    let mut ambiguity : Option String := none
    let mut disqualifyAuto := false
    if source.isAuto then
      if source.builtin == some .unpin then
        if let .definition .type "coroutine" _ _ := self then
          throw "coroutine Unpin requires source movability candidate assembly"
      for implementation in source.implementations do
        if ← liftM (RelevantImpl.possible (fuel + 1) implementation goal.traitRef) then
          disqualifyAuto := true
          break
    for implementation in source.implementations do
      let some bindings ← liftM (Match.head fuel implementation goal.traitRef environment.eraseRegions)
        | continue
      if implementation.isDefault then
        throw "default impl selection requires specialization semantics"
      let substitution ← liftM (Match.complete implementation.parameters environment.eraseRegions bindings)
      let predicates ← liftM (Substitution.clauses fuel substitution implementation.predicates)
      let mut results := #[]
      for predicate in predicates do
        results := results.push (← fulfillCore program hooks environment entryBoundary fuel active predicate)
      match collect results with
      | .noSolution => pure ()
      | .ambiguous reason => ambiguity := some reason
      | .proven (.conjunction proofs) =>
        if implementation.polarity == goal.polarity then
          candidates := candidates.push (.implementation ⟨implementation.definition, substitution⟩ proofs)
        else opposite := true
      | .proven _ => throw "trait conjunction evidence invariant violated"
    if goal.polarity == .positive && (source.isAuto || source.langItem.isSome) && !disqualifyAuto then
      if let some predicates ← liftM (hooks.builtin fuel active source goal) then
        let mut results := #[]
        for predicate in predicates do
          results := results.push (← fulfillCore program hooks environment entryBoundary fuel active predicate)
        match collect results with
        | .noSolution => pure ()
        | .ambiguous reason => ambiguity := some reason
        | .proven (.conjunction proofs) => candidates := candidates.push (.builtin goal proofs)
        | .proven _ => throw "builtin conjunction evidence invariant violated"
    if opposite && !candidates.isEmpty then return .ambiguous "opposite-polarity candidates both apply"
    if let some reason := ambiguity then return .ambiguous reason
    if opposite then
      if !environment.assumptions.isEmpty then
        return .ambiguous "environment elaboration may supply an opposite-polarity candidate"
      return .noSolution
    match candidates.size with
    | 0 =>
      if !environment.assumptions.isEmpty then
        return .ambiguous "environment super-clause elaboration is required"
      return .noSolution
    | 1 =>
      let some evidence := candidates[0]? | throw "unique trait candidate absent"
      return .proven evidence
    | _ => return .ambiguous "multiple applicable impl candidates require specialization"

private def fulfillCore (program : Program) (hooks : Hooks) (environment : Environment) (entryBoundary : Nat) :
    Nat → Array Goal → Clause → Engine Outcome
  | 0, _, _ => throw "trait fulfillment recursion exhausted"
  | fuel + 1, active, clause => do
    step
    unless clause.variables.isEmpty do throw "higher-ranked fulfillment requires universe instantiation"
    for index in [:environment.assumptions.size] do
      let some assumed := environment.assumptions[index]? | throw "environment clause index absent"
      if assumed.variables.isEmpty && decide (assumed.predicate = clause.predicate) then
        return .proven (.assumption index)
    match clause.predicate with
    | .trait goal => solveCore program hooks environment entryBoundary fuel active goal
    | .equal left right =>
      let left ← liftM (hooks.normalize fuel active left)
      let right ← liftM (hooks.normalize fuel active right)
      liftM (Match.requireGround fuel left)
      liftM (Match.requireGround fuel right)
      if left = right then return .proven (.equality left)
      if !environment.assumptions.isEmpty then
        return .ambiguous "environment equality closure is required"
      return .noSolution
    | .constHasType value expected =>
      let value ← liftM (hooks.normalize fuel active value)
      match value with
      | .node .constant "value" _ (.cons actual (.cons _ .nil)) =>
        unless actual.sort == .type do throw "evaluated constant source type is not a type"
        let actual ← liftM (hooks.normalize fuel active actual)
        let expected ← liftM (hooks.normalize fuel active expected)
        liftM (Match.requireGround fuel actual)
        liftM (Match.requireGround fuel expected)
        if actual = expected then return .proven (.equality actual)
        if !environment.assumptions.isEmpty then
          return .ambiguous "environment const-type equality closure is required"
        return .noSolution
      | _ => liftM (hooks.external fuel active environment clause.predicate)
    | .regionOutlives longer shorter =>
      if environment.eraseRegions then return .proven .regionErasure
      if longer = shorter then return .proven (.equality longer)
      liftM (hooks.external fuel active environment clause.predicate)
    | .typeOutlives .. =>
      if environment.eraseRegions then return .proven .regionErasure
      liftM (hooks.external fuel active environment clause.predicate)
    | _ => liftM (hooks.external fuel active environment clause.predicate)
end

/-- Each request starts with fresh work accounting; no result is reused across
executions. Ambiguity, unsupported providers and exhausted budgets are distinct
from both a proof and a definite negative trait result. -/
def solveWithActive (program : Program) (hooks : Hooks) (environment : Environment)
    (depth work : Nat) (active : Array Goal) (goal : Goal) : Except String Outcome :=
  (solveCore program hooks environment active.size depth active goal work).map (·.1)

def solve (program : Program) (hooks : Hooks) (environment : Environment)
    (depth work : Nat) (goal : Goal) : Except String Outcome :=
  solveWithActive program hooks environment depth work #[] goal

def fulfillWithActive (program : Program) (hooks : Hooks) (environment : Environment)
    (depth work : Nat) (active : Array Goal) (clauses : Array Clause) : Except String Outcome := do
  let (results, _) ← (do
    let mut results := #[]
    for clause in clauses do results := results.push (← fulfillCore program hooks environment active.size depth active clause)
    pure results : Engine (Array Outcome)) work
  pure (collect results)

def fulfill (program : Program) (hooks : Hooks) (environment : Environment)
    (depth work : Nat) (clauses : Array Clause) : Except String Outcome :=
  fulfillWithActive program hooks environment depth work #[] clauses

def selectUniqueWithActive (program : Program) (hooks : Hooks) (environment : Environment)
    (depth work : Nat) (active : Array Goal) (traitRef : TraitRef) : Except String ImplSelection := do
  match ← solveWithActive program hooks environment depth work active ⟨.positive, traitRef⟩ with
  | .proven (.implementation selection _) => pure selection
  | .proven _ => throw "trait proof does not identify a unique source impl"
  | .noSolution => throw "trait has no applicable source impl"
  | .ambiguous reason => throw s!"trait selection is ambiguous: {reason}"

def selectUnique (program : Program) (hooks : Hooks) (environment : Environment)
    (depth work : Nat) (traitRef : TraitRef) : Except String ImplSelection :=
  selectUniqueWithActive program hooks environment depth work #[] traitRef

/-- Positive source-parameter caller-bound fragment. Failure to prove a generic
caller-bound goal remains ambiguity; no impl/inference candidate is invented. -/
def solveWithSourceParameters (program : Program) (hooks : Hooks) (environment : Environment)
    (parameters : Array ArgSort) (depth work : Nat) (goal : Goal) : Except String Outcome := do
  if let some allowed := program.constructorScope then
    for argument in goal.traitRef.arguments do Match.requireConstructorScope allowed depth argument
  if goal.polarity == .positive then
    let proof ← EnvironmentEntailment.entails program parameters environment.assumptions work
      ⟨#[],.trait goal⟩
    if let some proof := proof then return .proven (.sourceEnvironment proof)
  if parameters.isEmpty then return (← solve program hooks environment depth work goal)
  return .ambiguous "source parameter environment fragment did not establish the trait goal"

end Miri.Input.TraitSelection
