import Miri.Input.Reader.Table
import Miri.Input.DecoderValues

namespace Miri.Input.Reader.LayoutReader
open Lean DecoderValues

abbrev Decode := ReaderT Catalog (Except String)

private def field (j : Json) (key path : String) : Decode Json := fun catalog => do
  catalog.inspect (← catalog.field j key path) (joinPath path key)

private def optionalField (j : Json) (key : String) : Decode (Option Json) := fun catalog => do
  (← catalog.optionalField j key "layout").mapM (fun value => catalog.inspect value s!"layout.{key}")

private def optionalJson (j : Json) (key : String) : Decode (Option Json) := do
  return (← optionalField j key).filter (· != .null)

private def fieldNat (j : Json) (key path : String) : Decode Nat := do
  (← field j key path).getNat?
private def fieldString (j : Json) (key path : String) : Decode String := do
  (← field j key path).getStr?
private def fieldBool (j : Json) (key path : String) : Decode Bool := do
  (← field j key path).getBool?
private def optionalNat (j : Json) (key path : String) : Decode (Option Nat) := do
  match ← optionalJson j key with
  | none => return none
  | some value => return some (← value.getNat?.mapError (fun error => s!"{joinPath path key}: {error}"))
private def optionalString (j : Json) (key path : String) : Decode (Option String) := do
  match ← optionalJson j key with
  | none => return none
  | some value => return some (← value.getStr?.mapError (fun error => s!"{joinPath path key}: {error}"))
private def jsonArray (j : Json) (path : String) : Decode (Array Json) := fun catalog =>
  catalog.array j path
private def natArray (j : Json) (path : String) : Decode (Array Nat) := fun catalog => do
  (← catalog.array j path).mapM (fun value => catalog.natural value path)
private def parseU128Natural (j : Json) (path : String) : Decode Nat := fun catalog => do
  DecoderValues.parseU128Natural (← catalog.inspect j path) path

private structure Tag where
  status : PayloadStatus
  tag : String
private def parseTagged (j : Json) (path : String) : Decode Tag := do
  let tag ← fieldString j "kind" path
  let status ← match ← optionalField j "status" with
    | none => pure .supported
    | some value => parseStatus <$> value.getStr?
  return ⟨status, tag⟩

def parsePrimitiveLayout (j : Json) (path : String) : Decode PrimitiveLayout := do
  let tag ← fieldString j "kind" path
  let kind := match tag with
    | "integer" => .integer
    | "float" => .float
    | "pointer" => .pointer
    | other => .unknown other
  let integerKindText ← optionalString j "integer_kind" path
  let integerKind := integerKindText.map integerTypeTag
  let signed ← match ← optionalField j "signed" with
    | none | some .null => pure none
    | some value => (value.getBool?).map some |>.mapError fun e => s!"{joinPath path "signed"}: expected boolean ({e})"
  let floatKindText ← optionalString j "float_kind" path
  let floatKind := floatKindText.map floatTypeTag
  let addressSpace ← optionalNat j "address_space" path
  return {
    kind := kind
    sizeBytes := ← fieldNat j "size_bytes" path
    integerKind := integerKind
    signed := signed
    floatKind := floatKind
    addressSpace := addressSpace
  }

/-- Exact compiler u128 encoding; preserve legacy JSON naturals while allowing
full-width decimal strings that serde_json cannot represent as numbers. -/

def parseScalarLayout (j : Json) (path : String) : Decode ScalarLayout := do
  let tag ← fieldString j "kind" path
  let kind := match tag with
    | "initialized" => .initialized
    | "union" => .union
    | other => .unknown other
  let range ← match ← optionalJson j "valid_range" with
    | none => pure none
    | some value => pure (some (← parseU128Natural (← field value "start" (joinPath path "valid_range")) (joinPath path "valid_range.start"), ← parseU128Natural (← field value "end" (joinPath path "valid_range")) (joinPath path "valid_range.end")))
  return {
    kind := kind
    primitive := ← parsePrimitiveLayout (← field j "primitive" path) (joinPath path "primitive")
    validRange := range
  }

def parseBackendRepr (j : Json) (path : String) : Decode BackendRepr := do
  let node ← parseTagged j path
  let tag := node.tag
  let kind := backendReprKind tag
  let scalar ← match ← optionalJson j "scalar" with
    | none => pure none
    | some value => pure (some (← parseScalarLayout value (joinPath path "scalar")))
  let first ← match ← optionalJson j "first" with
    | none => pure none
    | some value => pure (some (← parseScalarLayout value (joinPath path "first")))
  let second ← match ← optionalJson j "second" with
    | none => pure none
    | some value => pure (some (← parseScalarLayout value (joinPath path "second")))
  let element ← match ← optionalJson j "element" with
    | none => pure none
    | some value => pure (some (← parseScalarLayout value (joinPath path "element")))
  let sized ← match ← optionalField j "sized" with
    | none | some .null => pure none
    | some value => (value.getBool?).map some |>.mapError fun e => s!"{joinPath path "sized"}: expected boolean ({e})"
  let secondOffsetBytes ← optionalNat j "second_offset_bytes" path
  let laneCount ← optionalNat j "lane_count" path
  let vectorCount ← optionalNat j "vector_count" path
  match kind with
  | .scalar => if scalar.isNone then throw s!"{path}: scalar backend representation is missing scalar data"
  | .scalarPair =>
    if first.isNone || second.isNone || secondOffsetBytes.isNone then
      throw s!"{path}: scalar-pair backend representation is incomplete"
  | .memory => if sized.isNone then throw s!"{path}: memory backend representation is missing `sized`"
  | .simdVector | .scalableSimdVector =>
    if element.isNone || laneCount.isNone then throw s!"{path}: SIMD backend representation is incomplete"
  | .unknown _ => pure ()
  return {
    status := node.status
    kind := kind
    sized := sized
    scalar := scalar
    first := first
    second := second
    secondOffsetBytes := secondOffsetBytes
    element := element
    laneCount := laneCount
    vectorCount := vectorCount
  }

def parseFieldShape (j : Json) (path : String) : Decode FieldShape := do
  let tag ← fieldString j "kind" path
  let kind := match tag with
    | "primitive" => .primitive
    | "union" => .union
    | "array" => .array
    | "arbitrary" => .arbitrary
    | other => .unknown other
  let fieldCount ← optionalNat j "field_count" path
  let offsetBytes ← optionalNat j "offset_bytes" path
  let strideBytes ← optionalNat j "stride_bytes" path
  let offsetsBytes ← match ← optionalJson j "offsets_bytes" with
    | none => pure #[]
    | some value => natArray value (joinPath path "offsets_bytes")
  let memoryOrder ← match ← optionalJson j "memory_order" with
    | none => pure #[]
    | some value => natArray value (joinPath path "memory_order")
  let fieldCountValue := match fieldCount with | some count => count | none => 0
  match kind with
  | .primitive => pure ()
  | .union => if fieldCount.isNone || offsetBytes.isNone then throw s!"{path}: union field shape is incomplete"
  | .array => if fieldCount.isNone || strideBytes.isNone then throw s!"{path}: array field shape is incomplete"
  | .arbitrary =>
    if fieldCount.isNone || offsetsBytes.size != fieldCountValue || memoryOrder.size != fieldCountValue then
      throw s!"{path}: arbitrary field shape count/offset/order mismatch"
  | .unknown _ => pure ()
  return {
    kind := kind
    fieldCount := fieldCountValue
    offsetBytes := offsetBytes
    strideBytes := strideBytes
    offsetsBytes := offsetsBytes
    memoryOrder := memoryOrder
  }

def parseNicheLayout (j : Json) (path : String) : Decode (Option NicheLayout) := do
  if j == .null then return none
  let range ← field j "valid_range" path
  return some {
    offsetBytes := ← fieldNat j "offset_bytes" path
    primitive := ← parsePrimitiveLayout (← field j "primitive" path) (joinPath path "primitive")
    validRange := (← parseU128Natural (← field range "start" path) (joinPath path "valid_range.start"),
      ← parseU128Natural (← field range "end" path) (joinPath path "valid_range.end")) }

def parseLayoutVariant (j : Json) (path : String) : Decode LayoutVariant := do
  return {
    variantIndex := ← fieldNat j "variant_index" path
    sizeBytes := ← fieldNat j "size_bytes" path
    backendRepr := ← parseBackendRepr (← field j "backend_repr" path) (joinPath path "backend_repr")
    fieldOffsetsBytes := ← natArray (← field j "field_offsets_bytes" path) (joinPath path "field_offsets_bytes")
    fieldShape := ← parseFieldShape (← field j "fields" path) (joinPath path "fields")
    largestNiche := ← parseNicheLayout (← field j "largest_niche" path) (joinPath path "largest_niche")
    uninhabited := ← fieldBool j "uninhabited" path
  }

def parseTagEncoding (j : Json) (path : String) : Decode TagEncoding := do
  match j with
  | .obj _ =>
    let tag ← fieldString j "kind" path
    let status := parseStatus (← fieldString j "status" path)
    let kind := match tag with
      | "direct" => TagEncodingKind.direct
      | "niche" => TagEncodingKind.niche
      | other => TagEncodingKind.unknown other
    let untaggedVariant ← optionalNat j "untagged_variant" path
    let nicheVariants ← match ← optionalJson j "niche_variants" with
      | none => pure none
      | some range => pure (some (← fieldNat range "start" (joinPath path "niche_variants"), ← fieldNat range "end" (joinPath path "niche_variants")))
    let nicheStart ← match ← optionalField j "niche_start" with
      | none | some .null => pure none
      | some value =>
        let text ← value.getStr? |>.mapError fun e => s!"{joinPath path "niche_start"}: expected exact decimal string ({e})"
        pure (some (← decimalNat text (joinPath path "niche_start")))
    match kind with
    | .direct => pure ()
    | .niche =>
      if status == .supported && (untaggedVariant.isNone || nicheVariants.isNone || nicheStart.isNone) then
        throw s!"{path}: supported niche tag encoding is missing its range or start value"
    | .unknown _ => pure ()
    return ⟨status, kind, untaggedVariant, nicheVariants, nicheStart⟩
  | _ => throw s!"{path}: expected structured tag encoding"

def parseVariantsLayout (j : Json) (path : String) : Decode VariantsLayout := do
  let node ← parseTagged j path
  let tag := node.tag
  let kind := layoutVariantsKind tag
  let variantIndex ← optionalNat j "variant_index" path
  let scalarTag ← match ← optionalJson j "tag" with
    | none => pure none
    | some value => pure (some (← parseScalarLayout value (joinPath path "tag")))
  let tagEncoding ← match ← optionalJson j "tag_encoding" with
    | none => pure none
    | some value => pure (some (← parseTagEncoding value (joinPath path "tag_encoding")))
  let tagFieldIndex ← optionalNat j "tag_field_index" path
  let variantsJson ← match ← optionalJson j "variants" with
    | none => pure #[]
    | some value => jsonArray value (joinPath path "variants")
  let mut variants := #[]
  for (value, index) in variantsJson.toList.zipIdx do
    variants := variants.push (← parseLayoutVariant value s!"{joinPath path "variants"}[{index}]")
  match kind with
  | .single => if variantIndex.isNone then throw s!"{path}: single-variant layout is missing variant_index"
  | .multiple =>
    if scalarTag.isNone || tagEncoding.isNone || tagFieldIndex.isNone || variants.isEmpty then
      throw s!"{path}: multi-variant layout is missing tag or variant data"
  | .empty => pure ()
  | .unknown _ => pure ()
  return {
    status := node.status
    kind := kind
    variantIndex := variantIndex
    tag := scalarTag
    tagEncoding := tagEncoding
    tagFieldIndex := tagFieldIndex
    variants := variants
  }

def parseLayoutUncached (j : Json) (path : String) : Decode Layout := do
  let statusText ← fieldString j "status" path
  let status := parseStatus statusText
  let kind := match ← optionalString j "kind" path with
    | some "layout_query_error" => .layoutQueryError
    | some "layout" | none => .layout
    | some value => .unknown value
  let offsets ← if status == .supported then
    natArray (← field j "field_offsets_bytes" path) (joinPath path "field_offsets_bytes")
    else match ← optionalJson j "field_offsets_bytes" with
      | none => pure #[]
      | some value => natArray value (joinPath path "field_offsets_bytes")
  let fields ← match ← optionalJson j "fields" with
    | none => pure none
    | some value => pure (some (← parseFieldShape value (joinPath path "fields")))
  let variantsLayout ← match ← optionalJson j "variants" with
    | none => pure none
    | some value => pure (some (← parseVariantsLayout value (joinPath path "variants")))
  let backendRepresentation ← match ← optionalJson j "backend_repr" with
    | none => pure none
    | some value => pure (some (← parseBackendRepr value (joinPath path "backend_repr")))
  let sizeBytes ← optionalNat j "size_bytes" path
  let abiAlignBytes ← optionalNat j "abi_align_bytes" path
  let unadjustedAbiAlignBytes ← optionalNat j "unadjusted_abi_align_bytes" path
  let maxReprAlignBytes ← if status == .supported then do
      let value ← field j "max_repr_align_bytes" path
      if value == .null then pure none else pure (some (← value.getNat?))
    else optionalNat j "max_repr_align_bytes" path
  let boolean key := do
    match ← optionalField j key with
    | none | some .null =>
      if status == .supported then throw s!"{joinPath path key}: missing boolean"
      return none
    | some value => return some (← value.getBool?)
  let uninhabited ← boolean "uninhabited"
  let reprC ← boolean "repr_c"
  let randomizationSeed ← if status == .supported then some <$> fieldNat j "randomization_seed" path
    else optionalNat j "randomization_seed" path
  let largestNiche ← if status == .supported then
      parseNicheLayout (← field j "largest_niche" path) (joinPath path "largest_niche")
    else match ← optionalJson j "largest_niche" with
      | none => pure none
      | some value => parseNicheLayout value (joinPath path "largest_niche")
  if status == .supported && (sizeBytes.isNone || abiAlignBytes.isNone || unadjustedAbiAlignBytes.isNone) then
    throw s!"{path}: supported layout is missing size/alignment fields"
  if status == .supported && (fields.isNone || variantsLayout.isNone || backendRepresentation.isNone) then
    throw s!"{path}: supported layout is missing field/variant/backend representation data"
  match fields with
  | some fieldShape =>
    if fieldShape.fieldCount != offsets.size then
      throw s!"{path}: field shape count does not match field_offsets_bytes"
  | none => pure ()
  return {
    status := status
    kind := kind
    sizeBytes := sizeBytes
    abiAlignBytes := abiAlignBytes
    unadjustedAbiAlignBytes := unadjustedAbiAlignBytes
    maxReprAlignBytes := maxReprAlignBytes
    uninhabited := uninhabited
    reprC := reprC
    randomizationSeed := randomizationSeed
    largestNiche := largestNiche
    fieldOffsetsBytes := offsets
    fields := fields
    variantsLayout := variantsLayout
    backendRepresentation := backendRepresentation
  }

end Miri.Input.Reader.LayoutReader

namespace Miri.Input.Reader
open Lean Miri.MIR

def Catalog.decodeLayout (catalog : Catalog) (input : Json) (path : String) : Except String Layout :=
  LayoutReader.parseLayoutUncached input path catalog

def Catalog.readLayout (catalog : Catalog) (table : SharedTable Layout) (input : Json) (path : String) :
    Except String (Nat × SharedTable Layout) :=
  catalog.readEntry table (fun value => catalog.decodeLayout value path) input path

def Catalog.readTypeLayouts (catalog : Catalog) : Except String (Array Nat × SharedTable Layout) := do
  let types ← catalog.array (← catalog.field catalog.root "types" "$") "$.types"
  let mut table : SharedTable Layout := Array.replicate catalog.nodes.size none
  let mut ids := #[]
  for (type, index) in types.toList.zipIdx do
    let path := s!"$.types[{index}].layout"
    let (id, next) ← catalog.readLayout table (← catalog.field type "layout" path) path
    table := next
    ids := ids.push id
  return (ids, table)

end Miri.Input.Reader
