import Miri.Input.Model.SourceTypes
import Miri.Input.SourceTypeQueries
import Miri.Input.CompilerExternAbi
import Miri.Input.TableCore

/-! Initial ingestion of finite source types. JSON is consumed here and never
stored in the typed result. Unknown type/predicate tags are retained as explicit
unsupported variants; malformed required fields/references are errors. -/
namespace Miri.Frontend.Foundation.SourceTypesParser
open Lean Miri
open Input.SourceTypes
private def field := Json.getObjVal?
private def nat (j : Json) (k : String) := j.getObjValAs? Nat k
private def string (j : Json) (k : String) := j.getObjValAs? String k
private def array (j : Json) (k : String) := j.getObjValAs? (Array Json) k
private def optionalNat (j : Json) (k : String) : Except String (Option Nat) := do
  match j.getObjVal? k with
  | .error _ | .ok .null => pure none
  | .ok value => do pure (some (← value.getNat?))

def boundRegion (j : Json) : Except String BoundRegionKind := do
  match ← string j "kind" with
  | "anonymous" => pure .anonymous
  | "named" => return .named (← nat j "definition")
  | "named_for_printing" => return .namedForPrinting (← string j "name")
  | "closure_environment" => pure .closureEnvironment
  | _ => throw "Invalid source bound-region kind"
def region (j : Json) : Except String Region := do
  match j with
  | .str "static" => pure .static
  | .str "erased" => pure .erased
  | .str tag => pure (.unsupported tag)
  | _ =>
    match ← string j "kind" with
    | "early_parameter" => return .earlyParameter (← j.getObjValAs? Nat "index")
    | "bound" => return .bound (← nat j "debruijn") (← nat j "variable") (← boundRegion (← field j "region_kind"))
    | tag => pure (.unsupported tag)
def boundVariables (j : Json) : Except String (Array BoundVariable) := do
  (← j.getArr?).mapM fun entry => do
    match ← string entry "kind" with
    | "region" => return .region (← boundRegion (← field entry "region_kind"))
    | tag => return .unsupported tag

def signature (j : Json) : Except String Signature := do
  let safety ← match ← string j "safety" with
    | "safe" => pure MIR.Safety.Safe | "unsafe" => pure MIR.Safety.Unsafe
    | _ => throw "Invalid source signature safety"
  return ⟨← (← array j "inputs").mapM Json.getNat?, ← nat j "output", safety,
    ← Input.JsonReader.run Input.CompilerExternAbi.decode (← field j "abi").compress,
    ← j.getObjValAs? Bool "c_variadic", ← boundVariables (← field j "bound_variables")⟩

def constant (j : Json) : Except String ConstExpr := do
  match ← string j "kind" with
  | "alias" => return .alias (← nat j "reference")
  | "param" => return .parameter (← nat j "index") (← optionalNat j "type")
  | "value" =>
    let bits ← string j "bits"
    let some bits := bits.toNat? | throw "Invalid source scalar bits"
    return .value (← nat j "type") bits (← nat j "size_bytes")
  | tag => return .unsupported tag
def argument (j : Json) : Except String Argument := do
  match ← string j "kind" with
  | "type" => return .type (← nat j "type")
  | "region" => return .lifetime (← region (← field j "region"))
  | "const" => return .constant (← constant (← field j "value"))
  | _ => throw "Invalid source generic argument kind"
private def arguments (j : Json) : Except String (Array Argument) :=
  (j.getObjValAs? (Array Json) "arguments") >>= fun xs => xs.mapM argument
private def patternBound (j : Json) : Except String PatternBound := do
  if (← string j "kind") == "alias" then
    let kind ← match ← string j "alias_kind" with
      | "projection" => pure MIR.ConstAliasKind.Projection
      | "inherent_self" => pure .InherentSelf
      | "inherent_impl" => pure .InherentImpl
      | "free" => pure .Free
      | "anonymous" => pure .Anon
      | tag => throw s!"Invalid pattern bound const alias kind {tag}"
    let rigid ← match ← string j "rigidity" with
      | "rigid" => pure true
      | "not_rigid" => pure false
      | tag => throw s!"Invalid pattern bound const rigidity {tag}"
    return .alias rigid kind (← nat j "definition") (← arguments j)
  return .constant (← constant j)
private def mutable (j : Json) : Except String MIR.Mutability := do
  return if ← j.getObjValAs? Bool "mutable" then .Mut else .Not
private def existential (j : Json) : Except String ExistentialPredicate := do
  let tag ← string j "kind"
  match tag with
  | "trait" => return .trait (← nat j "definition") (← arguments j) (← boundVariables (← field j "bound_variables"))
  | "auto_trait" => return .autoTrait (← nat j "definition") (← boundVariables (← field j "bound_variables"))
  | "projection" =>
    let term ← field j "term"
    unless (← string term "kind") == "type" do return .unsupported "constant projection term"
    return .projection (← nat j "definition") (← nat j "parent_trait") (← arguments j)
      (← nat term "type") (← boundVariables (← field j "bound_variables"))
  | tag => return .unsupported tag

def expression (j : Json) : Except String Input.SourceTypes.Expr := do
  let tag ← string j "kind"
  match tag with
  | "bool" | "char" | "str" | "never" => return .primitive tag ""
  | "int" | "uint" | "float" => return .primitive tag (← string j "name")
  | "param" => return .parameter (← nat j "index") (← string j "name")
  | "array" => return .array (← nat j "element") (← constant (← field j "length"))
  | "tuple" => return .tuple (← (← array j "elements").mapM Json.getNat?)
  | "raw_pointer" => return .rawPointer (← nat j "pointee") (← mutable j)
  | "reference" => return .reference (← nat j "pointee") (← mutable j) (← region (← field j "region"))
  | "pattern_type" =>
    let pattern ← field j "pattern"
    match ← string pattern "kind" with
    | "not_null" => return .patternNotNull (← nat j "base")
    | "range" =>
      let lower ← patternBound (← field pattern "start")
      let upper ← patternBound (← field pattern "end")
      return .patternRange (← nat j "base") lower upper
    | _ => return .unsupported "constrained pattern"
  | "adt" => return .nominal (← nat j "definition") (← arguments j)
  | "dynamic" => return .dynamicObject (← region (← field j "region")) (← (← array j "predicates").mapM existential)
  | "function_pointer" => return .functionPointer (← signature (← field j "signature"))
  | "function_definition" => return .functionDefinition (← nat j "definition") (← arguments j)
  | "projection_alias" => return .projectionAlias (← nat j "definition") (← nat j "parent_trait") (← arguments j)
  | "closure" => return .closure ⟨← nat j "definition", ← nat j "parent_definition", ← nat j "parent_count",
      ← arguments j, ← nat j "kind_type", ← nat j "signature_type", ← nat j "tupled_upvars_type"⟩
  | tag => return .unsupported tag

private def representation (j : Json) : Except String Input.ReprOptions :=
  Input.JsonReader.run Input.DecoderValues.decodeCompilerReprOptions j.compress
private def discriminant (j : Json) : Except String Discriminant := do
  match ← string j "kind" with
  | "relative" => return .relative (← nat j "distance")
  | "explicit" => return .explicit (← nat j "definition")
  | _ => throw "Invalid source enum discriminant syntax"
private def variant (j : Json) (index : Nat) : Except String Variant := do
  if let some actual ← optionalNat j "index" then
    unless actual == index do throw "Invalid source variant index/order"
  let fields ← (← array j "fields").mapIdxM fun index f => do
    if let some actual ← optionalNat f "index" then
      unless actual == index do throw "Invalid source field index/order"
    return (⟨index,← optionalNat f "definition",← string f "name",← nat f "type"⟩ : Field)
  let constructor ← match j.getObjVal? "constructor" with
    | .error _ | .ok .null => pure none
    | .ok value => do pure (some (⟨← nat value "definition",← string value "kind"⟩ : Input.SourceTypes.Constructor))
  let fieldsNonExhaustive ← match j.getObjVal? "fields_non_exhaustive" with
    | .error _ | .ok .null => pure none
    | .ok value => do pure (some (← fromJson? value))
  let discr ← match j.getObjVal? "discriminant" with
    | .error _ | .ok .null => pure Discriminant.absent
    | .ok value => discriminant value
  return ⟨index,← optionalNat j "definition",← string j "name",constructor,fields,fieldsNonExhaustive,discr⟩
private def adt (j : Json) (owner : Nat) : Except String Adt := do
  let kind ← match ← string j "kind" with
    | "struct" => pure Input.AdtKind.structKind | "enum" => pure Input.AdtKind.enumKind
    | "union" => pure Input.AdtKind.unionKind | _ => throw "Invalid source ADT category"
  let environment ← field j "environment"
  unless (← nat environment "owner") == owner do throw "Invalid source ADT generic owner"
  let mut parameters := #[]
  for layer in ← array environment "layers" do
    unless (← nat layer "parent_count") == parameters.size do throw "Invalid source ADT generic layer count"
    for parameter in ← array layer "parameters" do
      unless (← nat parameter "index") == parameters.size do throw "Invalid source ADT generic parameter index"
      let parameter ← match ← string parameter "kind" with
        | "lifetime" => pure Input.SourceSymbols.ParameterKind.region
        | "type" => pure .typeParameter | "const" => pure .constParameter
        | _ => throw "Invalid source ADT parameter kind"
      parameters := parameters.push parameter
  let variants ← (← array j "variants").mapIdxM fun i v => variant v i
  let nonExhaustive ← match j.getObjVal? "variants_non_exhaustive" with
    | .error _ | .ok .null => pure none
    | .ok value => do pure (some (← fromJson? value))
  return ⟨kind,← representation (← field j "representation"),parameters,variants,nonExhaustive⟩
private def definition (j : Json) (index : Nat) : Except String Definition := do
  unless (← nat j "definition_id") == index do throw "Invalid source definition index/order"
  let raw : Input.DefinitionId := ⟨← nat j "crate_index",← nat j "index"⟩
  unless raw.crateIndex < 2^32 && raw.index < 2^32 do throw "Invalid source raw DefId width"
  let data ← match j.getObjVal? "adt" with
    | .error _ | .ok .null => pure none
    | .ok value => do pure (some (← adt value index))
  let auto ← match j.getObjVal? "trait_is_auto" with
    | .error _ | .ok .null => pure none
    | .ok value => do pure (some (← fromJson? value))
  return ⟨raw,← string j "kind",← string j "path",data,auto⟩
private def metadataStruct (j : Json) (count : String) : Except String MetadataStruct := do
  return ⟨← nat j "definition",← representation (← field j "repr"),← nat j "field_count",← nat j count⟩
private def dynMetadata (j : Json) : Except String DynMetadata := do
  match ← string j "mode" with
  | "metadata_lang_item_absent" => pure .metadataLangItemAbsent
  | "lang_item_declarations" =>
    let dynamic ← field j "dyn_metadata"
    let nonnull ← field j "non_null"
    let phantom ← field j "phantom_data"
    let p ← field nonnull "field"
    let pointer ← if (← string p "kind") == "pattern" && (← string p "pattern") == "not_null" &&
        (← string p "base_kind") == "raw_pointer" && (← string p "pointee_kind") == "foreign" then do
      pure (MetadataPointer.notNullRawForeign (← p.getObjValAs? Bool "mutable") (← nat p "pointee_definition"))
      else pure (.unsupported (← string p "kind") (← string p "pattern") (← string p "base_kind") (← string p "pointee_kind"))
    let argument ← field phantom "argument"
    unless (← string argument "kind") == "param" do return .unsupported "phantom argument"
    return .declarations ⟨← nat j "metadata_type",← nat j "pointee_trait",← nat j "metadata_parent",
      ← nat j "pointee_parameter_count",← nat j "metadata_parameter_count",← metadataStruct dynamic "parameter_count",
      ← nat dynamic "parameter_count",← nat dynamic "vtable_field",← nat dynamic "phantom_field",
      ← metadataStruct nonnull "argument_count",← string nonnull "lang_item",pointer,
      ← metadataStruct phantom "argument_count",← string phantom "lang_item",← nat argument "index"⟩
  | tag => return .unsupported tag

/-- Parse every source row once. Unsupported tags remain typed deferred errors. -/
def material (root : Json) : Except String Material := do
  let definitions ← (← array root "definitions").mapIdxM fun i j => definition j i
  let types ← (← array root "types").mapIdxM fun i j => do
    unless (← nat j "type_id") == i do throw "Invalid source type index/order"
    expression (← field j "shape")
  let aliases ← match root.getObjVal? "constant_aliases" with
    | .error _ => pure #[]
    | .ok rows => (← rows.getArr?).mapM fun row => do
      let kind ← match ← string row "kind" with
        | "projection" => pure MIR.ConstAliasKind.Projection
        | "inherent_self" => pure .InherentSelf
        | "inherent_impl" => pure .InherentImpl
        | "free" => pure .Free
        | "anonymous" => pure .Anon
        | tag => throw s!"Invalid source const alias kind {tag}"
      let rigid ← row.getObjValAs? Bool "rigid"
      let definition ← nat row "definition"
      let typeRef ← nat row "type"
      let args ← arguments row
      return (⟨rigid,kind,definition,typeRef,args,none⟩ : ConstantAlias)
  let metadata ← match root.getObjVal? "dyn_metadata_source" with
    | .error _ | .ok .null => pure none
    | .ok value => do pure (some (← dynMetadata value))
  let result : Material := {types,definitions,dynMetadata := metadata,constantAliases := aliases}
  result.validate
  return result
end Miri.Frontend.Foundation.SourceTypesParser
