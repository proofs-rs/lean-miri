import Miri.Input.TraitSelection.Substitution

/-! Declaration-template alias reduction. Sources: pinned rustc
`traits/normalize.rs::{normalize_free_alias,fold_ty}` and
`traits/project.rs::confirm_impl_candidate`. Definitions carry original RHS syntax; own obligations are obtained from
the canonical source scope when requested, never copied into reduction rules.
Associated selection and predicate fulfillment are mandatory callbacks to the
trait engine. This module does not implement that engine, specialization argument
translation, opaque hidden-type inference, const evaluation or the new solver's
context-sensitive rigid aliases. Those boundaries fail explicitly.
Inputs must already have the caller's intended region-erasure treatment. -/
namespace Miri.Input.AliasNormalization
open GenericSubstitution
open TraitSelection (Clause)

inductive Kind where
  | free | projection | inherent
  deriving Repr, DecidableEq, BEq
structure Key where
  kind : Kind
  definition : DefinitionIdentity
  arguments : Array Term
  deriving Repr, DecidableEq, BEq
structure Rule where
  definition : DefinitionIdentity
  template : DefinitionTemplate
structure AssociatedDeclaration where
  definition : DefinitionIdentity
  parent : DefinitionIdentity
  parentParameterCount : Nat
structure AssociatedValue where
  traitDefinition : DefinitionIdentity
  rule : Option Rule
  requiresHiddenTypeInference : Bool
  materialRetained : Bool
structure SelectedImpl where
  definition : DefinitionIdentity
  substitution : Array Term
  associatedValues : Array AssociatedValue
/-- Bridge a real trait-engine selection to original associated RHS templates.
It does not accept an instantiated type answer from the selector. -/
def fromTraitSelection (source : TraitSelection.Impl) (selection : TraitSelection.ImplSelection) :
    Except String SelectedImpl := do
  unless source.definition == selection.implementation do
    throw "associated selection does not identify its raw implementation"
  unless source.polarity == .positive do throw "associated selection is not a positive implementation"
  unless source.parameters.size == selection.substitution.size do
    throw "associated selection substitution count mismatch"
  for (expected, argument) in source.parameters.zip selection.substitution do
    unless expected == argument.sort do throw "associated selection substitution sort mismatch"
  let values := source.associatedValues.map fun value =>
    ({
      traitDefinition := value.traitAssociatedDefinition,
      rule := value.expression.map fun expression => {
        definition := value.implementationDefinition,
        template := expression},
      requiresHiddenTypeInference := value.requiresHiddenTypeInference,
      materialRetained := value.materialRetained} : AssociatedValue)
  pure ⟨source.definition, selection.substitution, values⟩

structure Program where
  freeRules : Array Rule
  associatedDeclarations : Array AssociatedDeclaration
structure Hooks where
  /-- Pinned own-obligation query, from the canonical raw declaration scope. -/
  ownPredicates : DefinitionIdentity → Except String (Array Clause)
  /-- Select from complete raw impl declarations. Overlap, ambiguity, absent
  predicates and unsupported specialization may not return a guessed winner. -/
  select : Nat → Array Key → Kind → DefinitionIdentity → Array Term → Except String SelectedImpl
  /-- Prove every instantiated own-clause obligation; no default callback exists. -/
  fulfill : Nat → Array Key → Array Clause → Except String Unit

def termsToArray : Terms → Array Term
  | .nil => #[]
  | .cons head tail => #[head] ++ termsToArray tail

private def aliasKind (tag : String) : Except String (Option Kind) := do
  if tag == "alias_free_not_rigid" then return some .free
  if tag == "alias_projection_not_rigid" then return some .projection
  if tag == "alias_inherent_not_rigid" then return some .inherent
  if tag.startsWith "alias_opaque_" then throw "opaque normalization requires hidden-type constraint inference"
  if tag.startsWith "alias_" then throw "rigid or unknown alias requires its solver mode and environment"
  pure none

private def containsBound : Nat → Term → Except String Bool
  | 0, _ => .error "alias bound-variable inspection exhausted"
  | fuel + 1, value => do
    match value with
    | .bound .. | .placeholder .. => pure true
    | .binder _ body => containsBound fuel body
    | .node _ _ _ children | .definition _ _ _ children => children.anyM (containsBound fuel)
    | _ => pure false

private def clauseTerms : TraitSelection.Predicate → Array Term
  | .trait goal => goal.traitRef.arguments
  | .hostEffect _ reference => reference.arguments
  | .equal left right | .regionOutlives left right | .typeOutlives left right
  | .constHasType left right => #[left,right]
  | .projection _ _ arguments expected => arguments.push expected
  | .constEvaluatable value | .wellFormed value => #[value]
  | .unstableFeature _ => #[]

structure Progress where
  value : Term
  obligations : Array Clause := #[]

mutual
private def fold (program : Program) (hooks : Hooks) :
    Nat → Array Key → Term → Except String Progress
  | 0, _, _ => .error "alias normalization recursion exhausted"
  | fuel + 1, active, value => do
    match value with
    | .definition .type tag definition children =>
      let some kind ← aliasKind tag
        | do
          let (children, obligations) ← foldTerms program hooks fuel active children
          return ⟨.definition .type tag definition children, obligations⟩
      -- Free aliases instantiate before folding the RHS. Eagerly normalizing
      -- unused arguments would introduce spurious cycles absent from rustc.
      let (arguments, argumentObligations) ← if kind == .free then
          pure (termsToArray children, #[])
        else do
          let (children, obligations) ← foldTerms program hooks fuel active children
          pure (termsToArray children, obligations)
      let key : Key := ⟨kind,definition,arguments⟩
      if active.contains key then throw "alias normalization cycle"
      let active := active.push key
      let (rule, substitutions, predicateSource, predicateArguments) ← if kind == .free then do
        let rules := program.freeRules.filter (·.definition == definition)
        unless rules.size == 1 do throw "free alias declaration RHS absent or duplicated"
        let some rule := rules[0]? | throw "free alias declaration RHS absent"
        pure (rule,arguments,← hooks.ownPredicates rule.definition,arguments)
      else do
        for argument in arguments do
          if ← containsBound (fuel + 1) argument then
            throw "associated normalization under bound variables requires placeholder conversion"
        let declarations := program.associatedDeclarations.filter (·.definition == definition)
        unless declarations.size == 1 do throw "associated declaration absent or duplicated"
        let some declaration := declarations[0]? | throw "associated declaration absent"
        unless declaration.parentParameterCount <= arguments.size do
          throw "associated parent generic prefix exceeds argument count"
        let selected ← hooks.select fuel active kind declaration.parent
          (arguments.extract 0 declaration.parentParameterCount)
        let values := selected.associatedValues.filter (·.traitDefinition == definition)
        unless values.size == 1 do
          throw "associated impl RHS absent, inherited, or duplicated"
        let some selectedValue := values[0]? | throw "associated impl RHS absent"
        if selectedValue.requiresHiddenTypeInference then
          throw "associated RHS requires hidden-type constraint inference"
        unless selectedValue.materialRetained do throw "associated RHS source material not retained"
        let some rule := selectedValue.rule | throw "associated source RHS template absent"
        let substitutions := selected.substitution ++ arguments.extract
          declaration.parentParameterCount arguments.size
        -- project.rs::assoc_term_own_obligations uses the trait item's own
        -- clauses with projection args, not impl-RHS clauses with impl args.
        pure (rule,substitutions,← hooks.ownPredicates declaration.definition,arguments)
      rule.template.checkArguments substitutions
      let predicates ← TraitSelection.Substitution.clauses (fuel + 1) predicateArguments predicateSource
      if !predicates.isEmpty then
        for argument in predicateArguments do
          if ← containsBound (fuel + 1) argument then
            throw "alias own clauses require bound-variable placeholder conversion"
      let rhs ← rule.template.instantiateType (fuel + 1) substitutions
      let result ← fold program hooks fuel active rhs
      -- rustc registers own clauses, folds the RHS, then fulfills at the query
      -- boundary. Fulfilling while this alias is active would add false cycles.
      return ⟨result.value, argumentObligations ++ predicates ++ result.obligations⟩
    | .definition .constant tag definition children =>
      if tag.startsWith "alias_" then throw "constant alias normalization requires const evaluation"
      let (children, obligations) ← foldTerms program hooks fuel active children
      return ⟨.definition .constant tag definition children, obligations⟩
    | .definition sort tag definition children =>
      let (children, obligations) ← foldTerms program hooks fuel active children
      return ⟨.definition sort tag definition children, obligations⟩
    | .node sort tag payload children =>
      let (children, obligations) ← foldTerms program hooks fuel active children
      return ⟨.node sort tag payload children, obligations⟩
    | .binder variables body =>
      let result ← fold program hooks fuel active body
      unless variables.isEmpty do
        for obligation in result.obligations do
          unless obligation.variables.isEmpty do
            throw "bound alias obligations require placeholder conversion"
          for argument in clauseTerms obligation.predicate do
            if ← containsBound (fuel + 1) argument then
              throw "bound alias obligations require placeholder conversion"
      return ⟨.binder variables result.value, result.obligations⟩
    | .inference .. => throw "alias normalization received unresolved inference material"
    | _ => pure ⟨value, #[]⟩

private def foldTerms (program : Program) (hooks : Hooks) :
    Nat → Array Key → Terms → Except String (Terms × Array Clause)
  | 0, _, _ => .error "alias normalization recursion exhausted"
  | _ + 1, _, .nil => pure (.nil, #[])
  | fuel + 1, active, .cons head tail => do
    let head ← fold program hooks fuel active head
    let (tail, rest) ← foldTerms program hooks fuel active tail
    pure (.cons head.value tail, head.obligations ++ rest)
end

/-- Closed alias normalization with mandatory fulfillment at the query boundary.
The stack is shared with trait selection; no cross-query or execution cache is
used. An error, ambiguous impl or unproved clause never returns a normalized type.
Region erasure and higher-ranked placeholder handling are separate prerequisites. -/
def normalize (program : Program) (hooks : Hooks) (fuel : Nat)
    (active : Array Key) (value : Term) : Except String Term := do
  let result ← fold program hooks fuel active value
  hooks.fulfill fuel active result.obligations
  pure result.value

end Miri.Input.AliasNormalization
