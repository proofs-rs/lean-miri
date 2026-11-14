import Miri.Input.WorldVTableSegments
import Miri.Input.RawFunctionSignature

/-! Concrete own-slot planning from raw declarations. A selected declaration is
an intermediate, not a final Instance: caller-location and reification policy
must still be applied before installing a runtime function pointer. -/
namespace Miri.Input.WorldVTableMethods
open GenericSubstitution TraitSelection

structure SelectedDeclaration where
  definition : DefinitionIdentity
  arguments : Array Term
  deriving Repr, DecidableEq

inductive Slot where
  | vacant
  | byValueShim (method : SelectedDeclaration)
  | selected (method : SelectedDeclaration)
  deriving Repr, DecidableEq

private def scope (context : AliasRuntime.Context) (fuel : Nat)
    (identity : DefinitionIdentity) : Except String SourceEnvironment.Material := do
  let source ← SourceEnvironmentRuntime.lookupDefinitions context.generic.definitions identity
  for clause in source.ownPredicates do
    HigherRankedMatch.validateSourceClause source.parameters fuel clause
  pure source

private def sourceDefinition (context : AliasRuntime.Context) (identity : DefinitionIdentity) :
    Except String DefinitionId := do
  let index ← GenericInstantiation.definitionRef context.generic identity
  let some source := context.generic.definitions[index]? | throw "vtable method source definition absent"
  pure source

private def signature (context : AliasRuntime.Context) (identity : DefinitionIdentity) :
    Except String RawFunctionSignature.Signature := do
  let source ← sourceDefinition context identity
  let some template := source.genericTemplate | throw "vtable method source template absent"
  let .definition .type "function_definition" owner _ := template.typeExpression
    | throw "vtable method source is not a function definition"
  unless owner == identity do throw "vtable method source physical identity mismatch"
  let some raw := template.signatureExpression | throw "vtable method raw signature absent"
  RawFunctionSignature.read raw

private def arguments (source : SourceEnvironment.Material) (parent : DefinitionIdentity)
    (parentArguments : Array Term) : Except String (Array Term) := do
  unless source.parent == source.genericParent do throw "vtable method source parent mismatch"
  let some owner := source.genericParent | throw "vtable method source generic parent absent"
  unless owner.definition == parent && owner.parameterCount == parentArguments.size do
    throw "vtable method source generic owner mismatch"
  unless parentArguments.size <= source.parameters.size do throw "vtable method source parentArguments exceeds header"
  let mut result := parentArguments
  for (sort,term) in (source.parameters.take parentArguments.size).zip parentArguments do
    unless sort == term.sort do throw "vtable method source argument sort mismatch"
  for sort in source.parameters.toList.drop parentArguments.size do
    unless sort == .region do throw "vtable method own type or const parameter is unsupported"
    result := result.push (.atom .region "erased" "")
  pure result

private def selected (context : AliasRuntime.Context) (work fuel : Nat)
    (declaration : TraitDeclaration) (reference : TraitRef) (member : TraitMember)
    (traitArguments : Array Term) : Except String SelectedDeclaration := do
  if declaration.implementations.any (·.isDefault) then
    throw "vtable method specialization requires its source ancestor provider"
  let selection ← AliasRuntime.selectGoal context fuel work reference
  let implementations := declaration.implementations.filter (·.definition == selection.implementation)
  unless implementations.size == 1 do throw "vtable selected impl source missing or ambiguous"
  let some implementation := implementations[0]? | throw "vtable selected impl source absent"
  let methods := implementation.methods.filter (·.traitAssociatedDefinition == member.definition)
  if methods.isEmpty then
    unless member.hasValue do throw "vtable selected impl has no method or trait default value"
    return ⟨member.definition,traitArguments⟩
  unless methods.size == 1 do throw "vtable selected impl method source is ambiguous"
  let some method := methods[0]? | throw "vtable selected impl method source absent"
  unless method.isFinal do throw "vtable selected method specialization requires its source leaf provider"
  let source ← scope context fuel method.implementationDefinition
  let actual ← arguments source implementation.definition selection.substitution
  let _ ← signature context method.implementationDefinition
  pure ⟨method.implementationDefinition,actual⟩

/-- Preserve every eligible own slot. Definitely false concrete predicates yield
Vacant; unresolved predicates error. Selected declarations still need the pinned
expect_resolve_for_vtable postprocessing before becoming runtime instances. -/
def ownSlots (context : AliasRuntime.Context) (work fuel : Nat) (reference : TraitRef) :
    Except String (Array Slot) := do
  let declarations := context.traits.traits.filter (·.definition == reference.definition)
  unless declarations.size == 1 do throw "vtable own trait source missing or ambiguous"
  let some declaration := declarations[0]? | throw "vtable own trait source absent"
  unless declaration.parameters.size == reference.arguments.size do throw "vtable concrete trait arity mismatch"
  let mut normalizedArguments := #[]
  for (sort,argument) in declaration.parameters.zip reference.arguments do
    unless sort == argument.sort do throw "vtable concrete trait argument sort mismatch"
    MirTemplate.validateClosed fuel argument
    let erased ← BinderRegions.eraseAndAnonymize fuel argument
    normalizedArguments := normalizedArguments.push
      (← AliasRuntime.normalizeTerm context work fuel #[] #[] erased)
  let reference := {reference with arguments := normalizedArguments}
  let methods ← WorldDynMethods.ownMethods context work fuel reference.definition
  let hooks := AliasRuntime.traitHooks context fuel (fun universeIndex remaining goals term =>
    AliasRuntime.normalizeTermScoped context universeIndex work remaining #[] goals term)
  let mut result := #[]
  for identity in methods do
    let members := declaration.members.filter (·.definition == identity)
    unless members.size == 1 do throw "vtable own method source missing or ambiguous"
    let some member := members[0]? | throw "vtable own method source absent"
    let source ← scope context fuel identity
    let actual ← arguments source declaration.definition reference.arguments
    -- rustc instantiate_and_check_impossible_clauses uses clauses_of, including
    -- inherited clauses, and explicitly adds Self:Trait. Canonical source
    -- parent traversal retains both; checking only own clauses misses even the
    -- absent-impl case before the early by-value VTable shim branch.
    let clauses ← SourceEnvironment.instantiate (scope context fuel) fuel identity actual
    match ← fulfill context.traits hooks {eraseRegions := true} fuel work clauses with
    | .noSolution => result := result.push .vacant
    | .ambiguous reason => throw s!"vtable concrete method predicates ambiguous: {reason}"
    | .proven _ =>
      let raw ← signature context identity
      if raw.inputs[0]? == some (.parameter .type 0) then
        let traitScope ← scope context fuel declaration.definition
        unless traitScope.isTrait && traitScope.parameters[0]? == some .type do
          throw "vtable by-value receiver has no canonical trait Self header"
        result := result.push (.byValueShim ⟨identity,actual⟩)
      else
        result := result.push (.selected (← selected context work fuel declaration reference member actual))
  pure result

end Miri.Input.WorldVTableMethods
