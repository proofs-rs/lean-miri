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
  | "reservation" => pure .reservation
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
    unless polarity != .reservation do throw "reservation is not a source clause polarity"
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

end Miri.Input.TraitSelection.Codec
