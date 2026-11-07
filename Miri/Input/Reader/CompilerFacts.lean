import Miri.Input.Reader.Table
import Miri.Input.DecoderValues

namespace Miri.Input.Reader.CompilerFactsReader
open Lean Miri.MIR
abbrev Decode := ReaderT Catalog (StateT CompilerFactTables (Except String))

private def field (input : Json) (key path : String) : Decode Json := fun catalog => do
  catalog.inspect (← catalog.field input key path) path
private def text (input : Json) (key path : String) : Decode String := do
  (← field input key path).getStr?
private def natural (input : Json) (key path : String) : Decode Nat := do
  (← field input key path).getNat?
private def boolean (input : Json) (key path : String) : Decode Bool := do
  (← field input key path).getBool?
private def status (input : Json) (path : String) : Decode PayloadStatus := do
  return DecoderValues.parseStatus (← text input "status" path)
private def rawField (input : Json) (key path : String) : Decode Json := fun catalog =>
  catalog.field input key path
private def optionalText (input : Json) (key path : String) : Decode (Option String) := fun catalog => do
  match ← catalog.optionalField input key path with
  | none | some .null => return none
  | some value => some <$> catalog.string value path
private def typeId (count : Nat) (input : Json) (path : String) : Decode Nat := do
  let id ← natural input "type_id" path
  unless id < count do throw s!"{path}: invalid type ID {id}"
  return id
private def cached (getTable : CompilerFactTables → SharedTable α)
    (putTable : CompilerFactTables → SharedTable α → CompilerFactTables)
    (decode : Json → String → Decode α) (input : Json) (path : String) : Decode Nat := fun catalog =>
  catalog.readCached getTable putTable (fun input path => decode input path catalog) input path

private def booleanValue (input : Json) (path : String) : Decode Nat :=
  cached (·.booleanValues) (fun state table => {state with booleanValues := table}) (fun input path => do
    let value ← field input "value" path
    return {
      status := (← status input path)
      value := (← if value == .null then pure none else some <$> value.getBool?)
      reason := (← optionalText input "reason" path) }) input path
private def typeValue (count : Nat) (input : Json) (path : String) : Decode Nat :=
  cached (·.typeValues) (fun state table => {state with typeValues := table}) (fun input path => do
    let value ← field input "value" path
    return {
      status := (← status input path)
      value := (← if value == .null then pure none else some <$> typeId count value path)
      reason := (← optionalText input "reason" path) }) input path
private def queryMap (decode : Json → String → Decode Nat)
    (getTable : CompilerFactTables → SharedTable (Array (String × Nat)))
    (putTable : CompilerFactTables → SharedTable (Array (String × Nat)) → CompilerFactTables)
    (input : Json) (path : String) : Decode Nat :=
  cached getTable putTable (fun input path => do
    let catalog ← read
    let .obj fields ← catalog.inspect input path | throw s!"{path}: expected query object"
    fields.toList.toArray.mapM fun (key,value) => do
      return (key,← decode value s!"{path}.{key}")) input path
private def names (input : Json) (path : String) : Decode Nat :=
  cached (·.captureNames) (fun state table => {state with captureNames := table}) (fun input path => do
    let catalog ← read
    let values ← catalog.array input path
    values.mapM fun value => do
      let value ← catalog.inspect value path
      if value == .null then pure none else some <$> value.getStr?) input path
private def discriminantValue (count : Nat) (input : Json) (path : String) : Decode Nat :=
  cached (·.discriminantValues) (fun state table => {state with discriminantValues := table}) (fun input path => do
    let variant ← natural input "variant" path
    unless variant < 2^32 do throw s!"{path}: variant index exceeds u32"
    let bits ← DecoderValues.parseU128Natural (.str (← text input "bits" path)) path
    return {variant, typeId := ← typeId count (← rawField input "type" path) path, bits}) input path
private def discriminantList (count : Nat) (input : Json) (path : String) : Decode Nat :=
  cached (·.discriminantLists) (fun state table => {state with discriminantLists := table}) (fun input path => do
    let catalog ← read
    let values ← catalog.array input path
    values.mapIdxM fun index value => discriminantValue count value s!"{path}[{index}]") input path
private def query (input : Json) (path : String) (decode : Json → Decode α) : Decode (Except String α) := do
  try
    unless (← status input path) == .supported do throw s!"{path}: compiler query unavailable"
    return .ok (← decode (← field input "value" path))
  catch reason => return .error reason
private def definition (input : Json) (path : String) : Decode DefinitionId := do
  return ⟨← natural input "crate" path,← natural input "index" path⟩

private def facts (count owner : Nat) (projection : Option Nat) (input : Json) (path : String) : Decode TypeCompilerFacts := do
  let inputTypeId ← typeId count (← rawField input "input_type" path) path
  unless inputTypeId == owner do throw s!"{path}: compiler fact owner mismatch"
  let typingEnvironment ← text input "typing_env" path
  unless typingEnvironment == "fully_monomorphized" do throw s!"{path}: invalid typing environment"
  let adt ← match ← field input "adt" path with
    | .null => pure none
    | value => some <$> do return {
        definition := ← definition (← rawField value "definition" path) path
        itemName := ← text value "item_name" path
        nonnullOptimizationGuaranteed := ← boolean value "nonnull_optimization_guaranteed" path }
  let definition ← match ← field input "definition" path with
    | .null => pure none | value => some <$> definition value path
  let capture ← field input "capture_names" path
  let captureStatus ← status capture path
  let captureValue ← rawField capture "value" path
  let catalog ← read
  let captureNames ← if (← catalog.inspect captureValue path) == .null then pure none else some <$> names captureValue path
  let simdSizeAndType ← query (← field input "simd_size_and_type" path) path fun value => do
    if value == .null then return none
    let lanes ← natural value "count" path
    unless lanes < 2^64 do throw s!"{path}: SIMD lane count exceeds u64"
    return some (lanes,← typeId count (← rawField value "element" path) path)
  let typeHash ← query (← field input "type_id_hash" path) path fun value =>
    do DecoderValues.parseU128Natural (.str (← value.getStr?)) path
  let discriminants ← query (← field input "discriminants" path) path fun value => do
    let variantCount ← field value "adt_variant_count" path
    return {
      hasDiscriminants := ← boolean value "has_discriminants" path
      adtVariantCount := ← if variantCount == .null then pure none else some <$> variantCount.getNat?
      values := ← discriminantList count (← rawField value "values" path) path }
  return {
    projectionQuery := projection, typingEnvironment, inputTypeId
    booleanQueries := ← queryMap booleanValue (·.booleanQueries) (fun state table => {state with booleanQueries := table}) (← rawField input "boolean_queries" path) path
    typeQueries := ← queryMap (typeValue count) (·.typeQueries) (fun state table => {state with typeQueries := table}) (← rawField input "type_queries" path) path
    adt, definition, captureNames, captureNamesStatus := some captureStatus, simdSizeAndType, typeHash, discriminants }

end Miri.Input.Reader.CompilerFactsReader

namespace Miri.Input.Reader
open Lean Miri.MIR

def Catalog.readCompilerFacts (catalog : Catalog) (projections : Array (Option Nat)) :
    Except String (Array (Option TypeCompilerFacts) × CompilerFactTables) := do
  let types ← catalog.array (← catalog.field catalog.root "types" "$") "$.types"
  let empty := fun {α : Type} => (Array.replicate catalog.nodes.size none : SharedTable α)
  let initial : CompilerFactTables := {
    booleanValues := empty, booleanQueries := empty, typeValues := empty, typeQueries := empty,
    captureNames := empty, discriminantValues := empty, discriminantLists := empty }
  let action : StateT CompilerFactTables (Except String) (Array (Option TypeCompilerFacts)) := types.mapIdxM fun index value => do
    let owner ← catalog.natural (← catalog.field value "type_id" "type") "type"
    let some projection := projections[index]? | throw "type projection query absent"
    match ← catalog.optionalField value "compiler_facts" "type" with
    | none | some .null => return none
    | some value => some <$> CompilerFactsReader.facts types.size owner projection value s!"$.types[{index}].compiler_facts" catalog
  action.run initial

end Miri.Input.Reader
