import Miri.Input.GenericMaterialCodec
import Miri.Input.TraitSelection.Material

/-! Strict raw source-clause decoding. Every pinned ClauseKind is represented;
unsupported semantics remain explicit constructors for the fulfillment engine.
No decoder branch turns an unknown or missing condition into a proven goal. -/
namespace Miri.Input.TraitSelection.Codec
open Lean (Json)
open GenericSubstitution

private def keys (value : Json) (allowed : List String) : Except String Unit := do
  for (key, _) in (← value.getObj?).toArray do
    unless allowed.contains key do throw s!"unknown raw trait material field {key}"

private def term (value : Json) : Except String Term := GenericMaterialCodec.readTerm 4096 value
private def arguments (value : Json) : Except String (Array Term) := do
  (← value.getArr?).mapM term
private def requireSort (value : Term) (sort : ArgSort) : Except String Unit := do
  unless value.sort == sort do throw "raw trait predicate argument sort mismatch"

def readPolarity (value : Json) : Except String Polarity := do
  match ← value.getStr? with
  | "positive" => pure .positive | "negative" => pure .negative
  | _ => throw "unknown raw trait polarity"

def readTraitRef (value : Json) : Except String TraitRef := do
  keys value ["definition", "arguments"]
  let definition ← GenericMaterialCodec.readDefinition (← value.getObjVal? "definition")
  let arguments ← arguments (← value.getObjVal? "arguments")
  let some self := arguments[0]? | throw "raw trait reference has no Self argument"
  requireSort self .type
  pure ⟨definition, arguments⟩

private def aliasKind (value : Json) : Except String AliasTermKind := do
  match ← value.getStr? with
  | "projection_type" => pure .projectionType | "inherent_type" => pure .inherentType
  | "opaque_type" => pure .opaqueType | "free_type" => pure .freeType
  | "anonymous_const" => pure .anonymousConst | "projection_const" => pure .projectionConst
  | "free_const" => pure .freeConst | "inherent_const_self" => pure .inherentConstSelf
  | "inherent_const_impl" => pure .inherentConstImpl
  | _ => throw "unknown raw projection alias kind"

def readPredicate (value : Json) : Except String Predicate := do
  let field (key : String) := value.getObjVal? key
  let tree (key : String) := field key >>= term
  match ← (← field "kind").getStr? with
  | "trait" => do
    keys value ["kind", "polarity", "trait_ref"]
    let polarity ← readPolarity (← field "polarity")
    return .trait ⟨polarity, ← readTraitRef (← field "trait_ref")⟩
  | "equal" => do
    keys value ["kind", "left", "right"]
    let left ← tree "left"
    let right ← tree "right"
    unless left.sort == right.sort && left.sort != .aggregate do
      throw "raw equality predicate argument sorts disagree"
    return .equal left right
  | "projection" => do
    keys value ["kind", "alias_kind", "associated", "arguments", "expected"]
    let kind ← aliasKind (← field "alias_kind")
    let associated ← GenericMaterialCodec.readDefinition (← field "associated")
    let arguments ← arguments (← field "arguments")
    let expected ← tree "expected"
    let expectedSort := match kind with
      | .projectionType | .inherentType | .opaqueType | .freeType => ArgSort.type
      | _ => ArgSort.constant
    requireSort expected expectedSort
    return .projection kind associated arguments expected
  | "region_outlives" => do
    keys value ["kind", "longer", "shorter"]
    let longer ← tree "longer"
    let shorter ← tree "shorter"
    requireSort longer .region
    requireSort shorter .region
    return .regionOutlives longer shorter
  | "type_outlives" => do
    keys value ["kind", "type", "region"]
    let ty ← tree "type"
    let region ← tree "region"
    requireSort ty .type
    requireSort region .region
    return .typeOutlives ty region
  | "const_evaluatable" => do
    keys value ["kind", "value"]
    let constant ← tree "value"
    requireSort constant .constant
    return .constEvaluatable constant
  | "const_has_type" => do
    keys value ["kind", "value", "type"]
    let constant ← tree "value"
    let ty ← tree "type"
    requireSort constant .constant
    requireSort ty .type
    return .constHasType constant ty
  | "well_formed" => do
    keys value ["kind", "value"]
    let value ← tree "value"
    unless value.sort == .type || value.sort == .constant do throw "raw well-formed term has invalid sort"
    return .wellFormed value
  | "host_effect" => do
    keys value ["kind", "requires_const", "trait_ref"]
    return .hostEffect (← (← field "requires_const").getBool?) (← readTraitRef (← field "trait_ref"))
  | "unstable_feature" => do
    keys value ["kind", "feature"]
    return .unstableFeature (← (← field "feature").getStr?)
  | other => throw s!"unknown raw trait predicate {other}"

def readClause (value : Json) : Except String Clause := do
  keys value ["variables", "predicate"]
  let variables ← (← (← value.getObjVal? "variables").getArr?).mapM GenericMaterialCodec.readVariable
  return ⟨variables, ← readPredicate (← value.getObjVal? "predicate")⟩

def readClauses (value : Json) : Except String (Array Clause) := do
  (← value.getArr?).mapM readClause


private def parameterSorts (value : Json) : Except String (Array ArgSort) := do
  let values ← (← value.getArr?).mapM GenericMaterialCodec.readSort
  unless values.all (· != .aggregate) do throw "aggregate is not a generic parameter sort"
  pure values

private def predicateTerms : Predicate → Array Term
  | .trait goal => goal.traitRef.arguments
  | .equal left right | .regionOutlives left right | .typeOutlives left right
  | .constHasType left right => #[left, right]
  | .projection _ _ arguments expected => arguments.push expected
  | .constEvaluatable value | .wellFormed value => #[value]
  | .hostEffect _ traitRef => traitRef.arguments
  | .unstableFeature _ => #[]

def validateClauses (parameters : Array ArgSort) (values : Array Clause) : Except String Unit := do
  for clause in values do
    for value in predicateTerms clause.predicate do
      GenericMaterialCodec.validateParameters parameters 4096 value

private def readAssociatedMethod (value : Json) : Except String AssociatedMethod := do
  keys value ["trait_associated_definition", "implementation_definition", "is_final"]
  return {
    traitAssociatedDefinition := ← GenericMaterialCodec.readDefinition (← value.getObjVal? "trait_associated_definition")
    implementationDefinition := ← GenericMaterialCodec.readDefinition (← value.getObjVal? "implementation_definition")
    isFinal := ← (← value.getObjVal? "is_final").getBool? }

/-- RHS templates are linked from the one canonical definition-material table.
The wire record contains declaration references, never a duplicated instantiated RHS. -/
private def readAssociatedValue (template : DefinitionIdentity → Except String (Option DefinitionTemplate))
    (value : Json) : Except String AssociatedValue := do
  keys value ["trait_associated_definition", "implementation_definition", "has_value",
    "requires_hidden_type_inference", "material_retained"]
  let traitAssociatedDefinition ← GenericMaterialCodec.readDefinition (← value.getObjVal? "trait_associated_definition")
  let implementationDefinition ← GenericMaterialCodec.readDefinition (← value.getObjVal? "implementation_definition")
  let hasValue ← (← value.getObjVal? "has_value").getBool?
  let requiresHiddenTypeInference ← (← value.getObjVal? "requires_hidden_type_inference").getBool?
  let materialRetained ← (← value.getObjVal? "material_retained").getBool?
  let expression ← if materialRetained && hasValue && !requiresHiddenTypeInference then do
      let some expression ← template implementationDefinition
        | throw "source associated RHS template reference absent"
      pure (some expression)
    else pure none
  pure {
    traitAssociatedDefinition := traitAssociatedDefinition
    implementationDefinition := implementationDefinition
    expression := expression
    requiresHiddenTypeInference := requiresHiddenTypeInference
    hasValue := hasValue
    materialRetained := materialRetained }

private def readImplementation (template : DefinitionIdentity → Except String (Option DefinitionTemplate))
    (value : Json) : Except String Impl := do
  keys value ["definition", "parameters", "trait_ref", "polarity", "is_default",
    "associated_values", "methods", "constants"]
  let definition ← GenericMaterialCodec.readDefinition (← value.getObjVal? "definition")
  let parameters ← parameterSorts (← value.getObjVal? "parameters")
  let traitRef ← readTraitRef (← value.getObjVal? "trait_ref")
  for argument in traitRef.arguments do
    GenericMaterialCodec.validateParameters parameters 4096 argument
  let polarity ← readPolarity (← value.getObjVal? "polarity")
  let isDefault ← (← value.getObjVal? "is_default").getBool?
  let associatedValues ← (← (← value.getObjVal? "associated_values").getArr?).mapM (readAssociatedValue template)
  let methods ← (← (← value.getObjVal? "methods").getArr?).mapM readAssociatedMethod
  let constants ← (← (← value.getObjVal? "constants").getArr?).mapM readAssociatedMethod
  let mut seen : Array DefinitionIdentity := #[]
  for item in associatedValues do
    if seen.contains item.traitAssociatedDefinition then throw "duplicate impl associated type declaration"
    seen := seen.push item.traitAssociatedDefinition
  pure {definition, parameters, traitRef, polarity, isDefault, associatedValues, methods, constants}

private def readMember (value : Json) : Except String TraitMember := do
  keys value ["definition", "kind", "has_value", "is_final", "is_method", "is_impl_trait_in_trait"]
  let kind ← (← value.getObjVal? "kind").getStr?
  unless ["type", "function", "constant"].contains kind do throw "unknown source associated member kind"
  let isMethod ← (← value.getObjVal? "is_method").getBool?
  let isImplTraitInTrait ← (← value.getObjVal? "is_impl_trait_in_trait").getBool?
  unless kind == "function" || !isMethod do throw "nonfunction source member claims a receiver"
  unless kind == "type" || !isImplTraitInTrait do throw "nontype source member claims RPITIT origin"
  return {
    definition := ← GenericMaterialCodec.readDefinition (← value.getObjVal? "definition")
    kind
    isMethod
    isImplTraitInTrait
    hasValue := ← (← value.getObjVal? "has_value").getBool?
    isFinal := ← (← value.getObjVal? "is_final").getBool? }

private def readTraitDeclaration (template : DefinitionIdentity → Except String (Option DefinitionTemplate))
    (value : Json) : Except String TraitDeclaration := do
  keys value ["definition", "parameters", "is_alias", "is_auto", "is_unsafe",
    "is_coinductive", "is_marker", "lang_item", "super_predicates", "implementations", "members"]
  let definition ← GenericMaterialCodec.readDefinition (← value.getObjVal? "definition")
  let parameters ← parameterSorts (← value.getObjVal? "parameters")
  unless parameters[0]? == some .type do throw "source trait declaration lacks Self type parameter"
  let isAlias ← (← value.getObjVal? "is_alias").getBool?
  let isAuto ← (← value.getObjVal? "is_auto").getBool?
  let isUnsafe ← (← value.getObjVal? "is_unsafe").getBool?
  let isCoinductive ← (← value.getObjVal? "is_coinductive").getBool?
  let isMarker ← (← value.getObjVal? "is_marker").getBool?
  let rawLang ← value.getObjVal? "lang_item"
  let langItem ← if rawLang == .null then pure none else pure (some (← rawLang.getStr?))
  let superPredicates ← readClauses (← value.getObjVal? "super_predicates")
  validateClauses parameters superPredicates
  let implementations ← (← (← value.getObjVal? "implementations").getArr?).mapM (readImplementation template)
  let members ← (← (← value.getObjVal? "members").getArr?).mapM readMember
  if isAlias && (!implementations.isEmpty || isAuto) then throw "trait alias has invalid auto/impl material"
  let mut seen : Array DefinitionIdentity := #[]
  for implementation in implementations do
    unless implementation.traitRef.definition == definition do throw "raw impl trait catalog mismatch"
    if seen.contains implementation.definition then throw "duplicate raw impl definition"
    seen := seen.push implementation.definition
  pure {
    definition := definition
    parameters := parameters
    isAlias := isAlias
    isAuto := isAuto
    isUnsafe := isUnsafe
    isCoinductive := isCoinductive
    isMarker := isMarker
    langItem := langItem
    superPredicates := superPredicates
    implementations := implementations
    members := members }

def readProgram (template : DefinitionIdentity → Except String (Option DefinitionTemplate))
    (value : Json) : Except String Program := do
  keys value ["traits", "constructor_scope"]
  let scope ← value.getObjVal? "constructor_scope"
  let kind ← (← scope.getObjVal? "kind").getStr?
  let constructorScope ← match kind with
    | "all_source_impls" => do
      keys scope ["kind"]
      pure none
    | "closed_source_constructors" => do
      keys scope ["kind", "constructors"]
      let constructors ← (← (← scope.getObjVal? "constructors").getArr?).mapM GenericMaterialCodec.readDefinition
      let mut seen : Array DefinitionIdentity := #[]
      for constructor in constructors do
        if seen.contains constructor then throw "duplicate trait source constructor scope identity"
        seen := seen.push constructor
      pure (some constructors)
    | _ => throw "unknown raw trait constructor scope"
  let traits ← (← (← value.getObjVal? "traits").getArr?).mapM (readTraitDeclaration template)
  let mut seen : Array DefinitionIdentity := #[]
  for declaration in traits do
    if seen.contains declaration.definition then throw "duplicate raw trait declaration"
    seen := seen.push declaration.definition
  pure {traits, constructorScope}

end Miri.Input.TraitSelection.Codec
