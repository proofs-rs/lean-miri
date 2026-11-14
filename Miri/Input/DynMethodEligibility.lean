import Miri.Input.TraitSelection.HigherRankedMatch
import Miri.Input.TraitSelection.Substitution
import Miri.Input.RawFunctionSignature

/-! Pinned dyn_compatibility.rs:70,317,437,689 and vtable.rs:202. This pure
leaf consumes source declarations. Receiver solving is a mandatory operation,
not a compiler eligibility answer or a guessed reference-receiver shortcut. -/
namespace Miri.Input.DynMethodEligibility
open GenericSubstitution TraitSelection

private def termsToArray : Terms → Array Term
  | .nil => #[]
  | .cons head tail => #[head] ++ termsToArray tail

structure Method where
  definition : DefinitionIdentity
  traitDefinition : DefinitionIdentity
  parameters : Array ArgSort
  parentParameterCount : Nat
  isMethod : Bool
  isFinal : Bool
  signature : Term
  ownClauses : Array Clause
  inheritedClauses : Array Clause

structure Projection where
  parent : DefinitionIdentity
  parentParameterCount : Nat
  isImplTraitInTrait : Bool

structure ReceiverQuery where
  parameters : Array ArgSort
  assumptions : Array Clause
  goal : Goal

structure Hooks where
  projection : DefinitionIdentity → Except String Projection
  /-- Expand raw abstract constant expressions before visiting their types. -/
  expandAbstractConst : Term → Except String Term
  /-- Normalize this unnormalized source param-env and prove the receiver
  DispatchFromDyn obligation modulo regions. Missing semantics must error. -/
  receiver : ReceiverQuery → Except String Bool
  constProjections : Option Bool

private def declaration (program : Program) (identity : DefinitionIdentity) :
    Except String TraitDeclaration := do
  let sources := program.traits.filter (·.definition == identity)
  unless sources.size == 1 do throw "dyn method source trait absent or ambiguous"
  let some source := sources[0]? | throw "dyn method source trait absent"
  pure source

private def langItem (program : Program) (name : String) : Except String (Option DefinitionIdentity) := do
  let sources := program.traits.filter (·.langItem == some name)
  unless sources.size <= 1 do throw "dyn method lang item identity ambiguous"
  let some source := sources[0]? | throw s!"dyn method required source lang item absent: {name}"
  pure (some source.definition)

/-- Region erasure at the current lexical depth, preserving regions owned by
nested binders, as EraseEscapingBoundRegions does for projection membership. -/
def eraseEscapingRegions : Nat → Nat → Term → Except String Term
  | 0,_,_ => throw "dyn method region traversal exhausted"
  | fuel + 1,depth,value => do
    if value.sort == .region then
      if let .bound .region (.Bound owner) .. := value then
        if owner < depth then return value
      return .atom .region "erased" ""
    match value with
    | .binder variables body => return .binder variables (← eraseEscapingRegions fuel (depth + 1) body)
    | .node sort tag payload children =>
      return .node sort tag payload (← children.mapM (eraseEscapingRegions fuel depth))
    | .definition sort tag identity children =>
      return .definition sort tag identity (← children.mapM (eraseEscapingRegions fuel depth))
    | _ => pure value

private def eraseReference (fuel : Nat) (value : TraitRef) : Except String TraitRef := do
  pure {value with arguments := ← value.arguments.mapM (eraseEscapingRegions fuel 0)}

/-- Elaborate raw positive superclauses without trait selection. Bound clauses
open in fresh local universes before substitution; they are never treated as
unconditional implementations. Exhaustion is an error, not absence of Sized. -/
def elaborate (program : Program) (parameters : Array ArgSort) (fuel : Nat)
    (clauses : Array Clause) : Except String (Array Clause) := do
  for clause in clauses do HigherRankedMatch.validateSourceClause parameters fuel clause
  let mut queue := clauses
  let mut seen : Array Clause := #[]
  let mut cursor := 0
  let mut lastUniverse := 0
  for _ in [:fuel] do
    let some clause := queue[cursor]? | return seen
    cursor := cursor + 1
    lastUniverse := lastUniverse + 1
    let clause ← if clause.variables.isEmpty then pure clause
      else Universes.openClause (Universes.enter lastUniverse) fuel clause
    if seen.any (fun prior => decide (prior = clause)) then continue
    seen := seen.push clause
    if let .trait ⟨.positive,reference⟩ := clause.predicate then
      let source ← declaration program reference.definition
      unless source.parameters.size == reference.arguments.size do
        throw "dyn method supertrait source arity mismatch"
      for (parameter,argument) in source.parameters.zip reference.arguments do
        unless parameter == argument.sort do throw "dyn method supertrait source sort mismatch"
      for raw in source.superPredicates do
        HigherRankedMatch.validateSourceClause source.parameters fuel raw
      queue := queue ++ (← Substitution.clauses fuel reference.arguments source.superPredicates)
  if cursor >= queue.size then pure seen else throw "dyn method source elaboration exhausted"

private def selfType : Term := .parameter .type 0

private def requiresSizedSelf (program : Program) (method : Method) (fuel : Nat) : Except String Bool := do
  let some sized ← langItem program "sized" | return false
  let clauses ← elaborate program method.parameters fuel (method.inheritedClauses ++ method.ownClauses)
  pure (clauses.any fun clause => match clause.predicate with
    | .trait ⟨_,reference⟩ => reference.definition == sized && reference.arguments[0]? == some selfType
    | _ => false)

private def superReferences (program : Program) (method : Method) (fuel : Nat) :
    Except String (Array TraitRef) := do
  let source ← declaration program method.traitDefinition
  let identity : TraitRef := ⟨source.definition,source.parameters.mapIdx fun index sort => .parameter sort index⟩
  let clauses ← elaborate program source.parameters fuel #[⟨#[],.trait ⟨.positive,identity⟩⟩]
  let mut result := #[]
  for clause in clauses do
    if let .trait ⟨.positive,reference⟩ := clause.predicate then
      result := result.push (← eraseReference fuel reference)
  pure result

private def illegalSelf (hooks : Hooks) (supers : Array TraitRef) : Nat → Term → Except String Bool
  | 0,_ => throw "dyn method Self traversal exhausted"
  | fuel + 1,term => do
    if term.sort == .constant then
      let expanded ← hooks.expandAbstractConst term
      if expanded != term then return ← illegalSelf hooks supers fuel expanded
    match term with
    | .parameter .type 0 => return true
    | .definition sort tag identity children =>
      let isProjection := tag == "alias_projection_rigid" || tag == "alias_projection_not_rigid"
      let allowProjection ← if sort == .type then pure true
        else if sort == .constant && isProjection then
          match hooks.constProjections with
          | some value => pure value
          | none => throw "dyn const projection source feature policy absent"
        else pure false
      if isProjection && allowProjection then
        let source ← hooks.projection identity
        if sort == .type && source.isImplTraitInTrait then return false
        let arguments := termsToArray children
        unless source.parentParameterCount <= arguments.size do throw "dyn projection parent prefix absent"
        let reference ← eraseReference fuel ⟨source.parent,arguments.take source.parentParameterCount⟩
        if supers.any (· == reference) then return false
      children.anyM (illegalSelf hooks supers fuel)
    | .node _ _ _ children => children.anyM (illegalSelf hooks supers fuel)
    | .binder _ body => illegalSelf hooks supers fuel body
    | _ => pure false

private def rpitit (hooks : Hooks) : Nat → Term → Except String Bool
  | 0,_ => throw "dyn method RPITIT traversal exhausted"
  | fuel + 1,term => do
    match term with
    | .definition .type tag identity children =>
      if tag == "alias_projection_rigid" || tag == "alias_projection_not_rigid" then
        if (← hooks.projection identity).isImplTraitInTrait then return true
      children.anyM (rpitit hooks fuel)
    | .definition _ _ _ children | .node _ _ _ children => children.anyM (rpitit hooks fuel)
    | .binder _ body => rpitit hooks fuel body
    | _ => pure false

private def predicateTerms : Predicate → Array Term
  | .trait goal => goal.traitRef.arguments
  | .hostEffect _ reference => reference.arguments
  | .equal left right | .regionOutlives left right | .typeOutlives left right
  | .constHasType left right => #[left,right]
  | .projection _ _ arguments expected => arguments.push expected
  | .constEvaluatable value | .wellFormed value => #[value]
  | .unstableFeature _ => #[]

private def receiverQuery (program : Program) (method : Method) (receiver : Term) (fuel : Nat) :
    Except String (Option ReceiverQuery) := do
  let some unsize ← langItem program "unsize" | return none
  let some dispatch ← langItem program "dispatch_from_dyn" | return none
  let some metaSized ← langItem program "meta_sized" | throw "dyn receiver MetaSized lang item absent"
  let traitSource ← declaration program method.traitDefinition
  let unknown : Term := .parameter .type method.parameters.size
  let arguments := method.parameters.mapIdx fun index sort =>
    if index == 0 then unknown else .parameter sort index
  let changed ← GenericSubstitution.instantiate fuel arguments receiver
  let traitArguments := arguments.take traitSource.parameters.size
  let traitGoal : Clause := ⟨#[],.trait ⟨.positive,⟨method.traitDefinition,traitArguments⟩⟩⟩
  let traitClauses ← Substitution.clauses fuel arguments method.inheritedClauses
  let traitClauses := traitClauses.filter fun clause => match clause.predicate with | .trait _ => true | _ => false
  pure (some ⟨method.parameters.push .type,
    method.inheritedClauses ++ method.ownClauses ++ #[
      ⟨#[],.trait ⟨.positive,⟨unsize,#[selfType,unknown]⟩⟩⟩,traitGoal] ++ traitClauses ++
      #[⟨#[],.trait ⟨.positive,⟨metaSized,#[unknown]⟩⟩⟩],
    ⟨.positive,⟨dispatch,#[receiver,changed]⟩⟩⟩)

def ownEntry (program : Program) (hooks : Hooks) (method : Method) (fuel : Nat) : Except String Bool := do
  unless method.parentParameterCount <= method.parameters.size do throw "dyn method generic parent exceeds header"
  let source ← declaration program method.traitDefinition
  let members := source.members.filter (·.definition == method.definition)
  unless members.size == 1 do throw "dyn method source member absent or duplicated"
  let some member := members[0]? | throw "dyn method source member absent"
  unless member.kind == "function" && member.isFinal == method.isFinal && member.isMethod == method.isMethod do
    throw "dyn method source member kind or finality mismatch"
  unless source.parameters == method.parameters.take method.parentParameterCount do
    throw "dyn method generic header is not its trait source prefix"
  GenericSyntax.validate {parameters := method.parameters,erasedRegions := true,lateRegions := true}
    fuel .signature method.signature
  for clause in method.inheritedClauses ++ method.ownClauses do
    HigherRankedMatch.validateSourceClause method.parameters fuel clause
  if method.isFinal then return false
  if ← requiresSizedSelf program method fuel then return false
  unless method.isMethod do return false
  let signature ← RawFunctionSignature.read method.signature
  let supers ← superReferences program method fuel
  for input in signature.inputs.toList.drop 1 do
    if ← illegalSelf hooks supers fuel input then return false
  if ← illegalSelf hooks supers fuel signature.output then return false
  if ← rpitit hooks fuel signature.output then return false
  if signature.cVariadic then return false
  if (method.parameters.toList.drop method.parentParameterCount).any (· != .region) then return false
  let some receiver := signature.inputs[0]? | throw "dyn method receiver source absent"
  let receiver ← eraseEscapingRegions fuel 0 receiver
  if receiver != selfType then
    let some query ← receiverQuery program method receiver fuel | return false
    unless ← hooks.receiver query do return false
  for clause in method.ownClauses do
    if let .typeOutlives .. := clause.predicate then continue
    if let .trait ⟨.positive,reference⟩ := clause.predicate then
      let source ← declaration program reference.definition
      if reference.arguments[0]? == some selfType && source.isAuto then
        unless reference.arguments.size == 1 do throw "dyn method auto trait source has extra arguments"
        continue
    if let .projection .projectionType identity arguments expected := clause.predicate then
      let projection := Term.definition .type "alias_projection_not_rigid" identity (Terms.ofArray arguments)
      if ← illegalSelf hooks supers fuel projection then return false
      if ← illegalSelf hooks supers fuel expected then return false
    else
      for term in predicateTerms clause.predicate do
        if ← illegalSelf hooks supers fuel term then return false
  pure true

end Miri.Input.DynMethodEligibility
