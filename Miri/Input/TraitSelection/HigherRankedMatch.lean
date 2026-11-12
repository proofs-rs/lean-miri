import Miri.Input.TraitSelection.Inference
import Miri.Input.GenericSyntax

/-! Equality matching of source impl heads with quantified trait references.
The forall side opens into fresh placeholders before impl parameters and the
existential side of nested binders are created. This module checks only the
head relation; where-clause fulfillment remains a mandatory separate operation.
Aliases and unevaluated constants require normalization before this relation. -/
namespace Miri.Input.TraitSelection.HigherRankedMatch
open GenericSubstitution

private def lift (value : Except String α) : Inference.M α :=
  match value with | .ok value => pure value | .error error => throw error

def requireNormalized : Nat → Term → Except String Unit
  | 0, _ => throw "quantified normalization-domain traversal exhausted"
  | fuel + 1, term => do
    match term with
    | .definition _ tag _ children =>
      if tag.startsWith "alias_" then throw "quantified impl relation requires normalized aliases"
      let _ ← children.mapM fun child => do requireNormalized fuel child; pure child
      pure ()
    | .node .constant tag _ children =>
      unless tag == "value" do throw "quantified impl relation requires evaluated constants"
      let _ ← children.mapM fun child => do requireNormalized fuel child; pure child
      pure ()
    | .node _ _ _ children =>
      let _ ← children.mapM fun child => do requireNormalized fuel child; pure child
      pure ()
    | .binder _ body => requireNormalized fuel body
    | _ => pure ()

private def regionEqual (eraseFreeRegions : Bool) (left right : Term) : Bool :=
  match left,right with
  | .placeholder .region lu li _,.placeholder .region ru ri _ => lu == ru && li == ri
  | .atom .region "static" "",.atom .region "static" "" => true
  | .atom .region "erased" "",.atom .region "erased" "" => true
  | .atom .region ..,.atom .region .. => eraseFreeRegions
  | _,_ => false

private def requireAllocated (maximumUniverse : Nat) : Nat → Term → Except String Unit
  | 0,_ => throw "quantified placeholder ownership traversal exhausted"
  | fuel + 1,value => do
    match value with
    | .placeholder _ universeIndex .. =>
      unless universeIndex > 0 && universeIndex <= maximumUniverse do
        throw "trait placeholder is outside its query universe"
    | .binder _ body => requireAllocated maximumUniverse fuel body
    | .node _ _ _ children | .definition _ _ _ children =>
      let _ ← children.mapM fun child => do requireAllocated maximumUniverse fuel child; pure child
      pure ()
    | _ => pure ()

def validateClause (maximumUniverse fuel : Nat) (eraseFreeRegions : Bool) (clause : Clause) :
    Except String Unit := do
  let policy : GenericSyntax.Policy := {
    placeholders := maximumUniverse != 0
    erasedRegions := eraseFreeRegions}
  let check := fun role term => do
    GenericSyntax.validateInBinders policy fuel #[clause.variables] role term
    requireAllocated maximumUniverse fuel term
  let argument := fun term => do
    let role ← match term.sort with
      | .type => pure GenericSyntax.Role.type | .region => pure .region
      | .constant => pure .constant | .aggregate => throw "aggregate predicate argument"
    check role term
  let reference := fun (value : TraitRef) => do
    let some self := value.arguments[0]? | throw "quantified trait Self is absent"
    unless self.sort == .type do throw "quantified trait Self is not a type"
    for term in value.arguments do argument term
  match clause.predicate with
  | .trait goal => reference goal.traitRef
  | .hostEffect _ value => reference value
  | .equal left right =>
    unless left.sort == right.sort do throw "quantified equality sort mismatch"
    argument left
    argument right
  | .projection kind _ arguments expected =>
    for term in arguments do argument term
    let role := match kind with
      | .projectionType | .inherentType | .opaqueType | .freeType => GenericSyntax.Role.type
      | _ => .constant
    check role expected
  | .regionOutlives longer shorter => check .region longer *> check .region shorter
  | .typeOutlives ty region => check .type ty *> check .region region
  | .constHasType value ty => check .constant value *> check .type ty
  | .constEvaluatable value => check .constant value
  | .wellFormed value =>
    unless value.sort == .type || value.sort == .constant do throw "quantified well-formed sort mismatch"
    argument value
  | .unstableFeature _ => pure ()

mutual
private def equalTerms (eraseFreeRegions : Bool) : Nat → Terms → Terms → Inference.M Bool
  | 0, _, _ => throw "quantified term equality exhausted"
  | _ + 1, .nil, .nil => pure true
  | fuel + 1, .cons left lefts, .cons right rights => do
    unless ← equalTerm eraseFreeRegions fuel left right do return false
    equalTerms eraseFreeRegions fuel lefts rights
  | _ + 1, _, _ => pure false

private def equalTerm (eraseFreeRegions : Bool) : Nat → Term → Term → Inference.M Bool
  | 0, _, _ => throw "quantified type equality exhausted"
  | fuel + 1, left, right => do
    let state ← get
    let left ← lift (Inference.resolve state (fuel + 1) left)
    let right ← lift (Inference.resolve state (fuel + 1) right)
    unless left.sort == right.sort do return false
    if let .inference _ id := left then return ← Inference.assign (fuel + 1) id right
    if let .inference _ id := right then return ← Inference.assign (fuel + 1) id left
    if left.sort == .region then return regionEqual eraseFreeRegions left right
    match left,right with
    | .binder leftVariables leftBody,.binder rightVariables rightBody =>
      let scope ← Inference.freshUniverse
      let right ← lift (Universes.openTerm rightVariables scope.current (fuel + 1) 0 rightBody)
      let left ← Inference.instantiateBinder scope.current (fuel + 1) leftVariables leftBody
      unless ← equalTerm eraseFreeRegions fuel left right do return false
      -- Equality requires both higher-ranked directions. One direction alone
      -- would accept `for<'a> fn(&'a u8)` as equal to `fn(&'static u8)`.
      let reverseScope ← Inference.freshUniverse
      let left ← lift (Universes.openTerm leftVariables reverseScope.current (fuel + 1) 0 leftBody)
      let right ← Inference.instantiateBinder reverseScope.current (fuel + 1) rightVariables rightBody
      equalTerm eraseFreeRegions fuel right left
    | .atom leftSort leftTag leftPayload,.atom rightSort rightTag rightPayload =>
      if leftSort != rightSort || leftTag != rightTag then return false
      if leftSort == .aggregate && leftTag == "scalar" then
        return (← lift (Lean.Json.parse leftPayload)) == (← lift (Lean.Json.parse rightPayload))
      pure (leftPayload == rightPayload)
    | .node leftSort leftTag leftPayload leftChildren,.node rightSort rightTag rightPayload rightChildren =>
      if leftSort != rightSort || leftTag != rightTag then return false
      if leftSort == .aggregate && leftTag == "signature" then
        let leftHeader ← lift (RawFunctionSignature.read (.binder #[] left))
        let rightHeader ← lift (RawFunctionSignature.read (.binder #[] right))
        unless leftHeader.abi == rightHeader.abi && leftHeader.safety == rightHeader.safety &&
            leftHeader.cVariadic == rightHeader.cVariadic && leftHeader.splatted == rightHeader.splatted do
          return false
      else if leftPayload != rightPayload then return false
      equalTerms eraseFreeRegions fuel leftChildren rightChildren
    | .definition leftSort leftTag leftIdentity leftChildren,
        .definition rightSort rightTag rightIdentity rightChildren =>
      if leftSort != rightSort || leftTag != rightTag || leftIdentity != rightIdentity then return false
      equalTerms eraseFreeRegions fuel leftChildren rightChildren
    | .placeholder leftSort lu li _,.placeholder rightSort ru ri _ =>
      pure (leftSort == rightSort && lu == ru && li == ri)
    | .parameter ..,_ | _,.parameter .. => throw "quantified relation retains an early parameter"
    | .bound ..,_ | _,.bound .. => throw "quantified relation retains an escaping bound variable"
    | _,_ => pure false
end

/-- Validate query-local placeholders against the caller's allocated universe
boundary. This does not authorize any raw inference identity. -/
def requireScoped (maximumUniverse fuel : Nat) (value : Term) : Except String Unit := do
  let role ← match value.sort with
    | .type => pure GenericSyntax.Role.type | .region => pure .region
    | .constant => pure .constant | .aggregate => throw "aggregate trait argument"
  GenericSyntax.validate {placeholders := true,erasedRegions := true} fuel role value
  requireAllocated maximumUniverse fuel value

/-- Match a goal already opened by quantified fulfillment. The supplied
universe boundary owns its placeholders; where clauses remain separate. -/
def headScoped (maximumUniverse fuel : Nat) (implementation : Impl) (goal : TraitRef)
    (eraseFreeRegions : Bool := false) : Except String (Option (Array Term)) := do
  if implementation.traitRef.definition != goal.definition then return none
  let implPolicy : GenericSyntax.Policy := {parameters := implementation.parameters,erasedRegions := eraseFreeRegions}
  for argument in implementation.traitRef.arguments do
    let role ← match argument.sort with
      | .type => pure GenericSyntax.Role.type | .region => pure .region
      | .constant => pure .constant | .aggregate => throw "aggregate impl argument"
    GenericSyntax.validate implPolicy fuel role argument
    requireNormalized fuel argument
  for argument in goal.arguments do
    requireScoped maximumUniverse fuel argument
    requireNormalized fuel argument
  let action : Inference.M (Option (Array Term)) := do
    let mut arguments := #[]
    for sort in implementation.parameters do
      arguments := arguments.push (← Inference.fresh sort maximumUniverse)
    let instantiated ← lift (implementation.traitRef.arguments.mapM (GenericSubstitution.instantiate fuel arguments))
    unless ← equalTerms eraseFreeRegions fuel (Terms.ofArray instantiated) (Terms.ofArray goal.arguments) do
      return none
    let state ← get
    unless ← lift (Inference.assignmentsVisible state fuel) do return none
    lift (Inference.checkLeaks state 0 fuel)
    let resolved ← lift (arguments.mapM (Inference.resolve state fuel))
    let rec complete : Nat → Term → Except String Unit
      | 0,_ => throw "quantified substitution completion exhausted"
      | fuel + 1,term => do
        match term with
        | .inference .. => throw "quantified impl parameter remains unconstrained"
        | .binder _ body => complete fuel body
        | .node _ _ _ children | .definition _ _ _ children =>
          let _ ← children.mapM fun child => do complete fuel child; pure child
          pure ()
        | _ => pure ()
    for argument in resolved do lift (complete fuel argument)
    pure (some resolved)
  pure (← action.run {lastUniverse := maximumUniverse}).1

/-- Raw quantified-clause entry point. Success establishes only the impl-head
relation, not fulfillment of that implementation's source where clauses. -/
def headClause (fuel : Nat) (implementation : Impl) (clause : Clause)
    (eraseFreeRegions : Bool := false) : Except String (Option (Array Term)) := do
  let .trait goal := clause.predicate | throw "quantified impl matching requires a trait clause"
  let goalPolicy : GenericSyntax.Policy := {erasedRegions := eraseFreeRegions}
  for argument in goal.traitRef.arguments do
    let role ← match argument.sort with
      | .type => pure GenericSyntax.Role.type | .region => pure .region
      | .constant => pure .constant | .aggregate => throw "aggregate quantified argument"
    GenericSyntax.validateInBinders goalPolicy fuel #[clause.variables] role argument
    requireNormalized fuel argument
  if clause.variables.isEmpty then
    headScoped 0 fuel implementation goal.traitRef eraseFreeRegions
  else
    let scope := Universes.enter 0
    let opened ← Universes.openClause scope fuel clause
    let .trait openedGoal := opened.predicate | throw "opened trait predicate disappeared"
    headScoped scope.current fuel implementation openedGoal.traitRef eraseFreeRegions

end Miri.Input.TraitSelection.HigherRankedMatch
