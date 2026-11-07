import Miri.Input.RuntimeMetadataError
import Miri.Input.Model
import Miri.Input.Decoder
import Miri.ABI.Layout

/-! Internal compiler-metadata bridge, not the public import API. Successful
conversion supplies records and queries; it does not establish execution
readiness, machine-hook adequacy, or Rust UB freedom. Original source nodes
remain available beside every canonical layout result. -/
namespace Miri.Input
open Miri.ABI


namespace RuntimeMetadata

abbrev Result := Except RuntimeMetadataError

def require (value : Option A) (path : String) : Result A :=
  match value with | some value => pure value | none => throw (.missing path)
private def convert (path : String) (result : Except String A) : Result A :=
  result.mapError (.invalid path)
def jsonField (j : Lean.Json) (name : String) : Result Lean.Json :=
  convert name (j.getObjVal? name)
def number (j : Lean.Json) (name : String) : Result Nat := do
  convert name ((← jsonField j name).getNat?)
/-- Full-width rustc u128 JSON endpoints, with backward numeric encoding. -/
def u128Number (j : Lean.Json) (name : String) : Result Nat := do
  let value ← jsonField j name
  let natural ← match value with
    | .str text =>
      unless !text.isEmpty && text.toList.all Char.isDigit do throw (.invalid name "expected exact unsigned decimal")
      match text.toNat? with
      | some value => pure value
      | none => throw (.invalid name "invalid unsigned decimal")
    | _ => convert name value.getNat?
  unless natural < 2^128 do throw (.invalid name "u128 overflow")
  pure natural
def truth (j : Lean.Json) (name : String) : Result Bool := do
  convert name ((← jsonField j name).getBool?)
def text (j : Lean.Json) (name : String) : Result String := do
  convert name ((← jsonField j name).getStr?)
def array (j : Lean.Json) (name : String) : Result (Array Lean.Json) := do
  convert name ((← jsonField j name).getArr?)
def u64 (n : Nat) (path : String) : Result UInt64 :=
  if n < 2^64 then pure (UInt64.ofNat n) else throw (.invalid path "u64 overflow")
def u32 (n : Nat) (path : String) : Result UInt32 :=
  if n < 2^32 then pure (UInt32.ofNat n) else throw (.invalid path "u32 overflow")
def u128 (n : Nat) (path : String) : Result U128 :=
  if n < 2^128 then pure (BitVec.ofNat 128 n) else throw (.invalid path "u128 overflow")
def size (n : Nat) : Result Size := Size.ofBytes <$> u64 n "size"
def alignment (n : Nat) : Result Align := do
  if n == 0 then throw (.invalid "alignment" "zero alignment")
  (Align.fromBytes (← u64 n "alignment")).mapError (fun e => .invalid "alignment" (toString e))

def integer : MIR.IntegerKind → Result Integer
  | .i8 | .u8 => pure .I8
  | .i16 | .u16 => pure .I16
  | .i32 | .u32 => pure .I32
  | .i64 | .u64 => pure .I64
  | .i128 | .u128 => pure .I128
  | .isize | .usize => throw (.unsupported "pointer-sized integer primitive tag")
def float : FloatTypeTag → Result ABI.Float
  | .f16 => pure .F16 | .f16b => pure .F16B | .f32 => pure .F32
  | .f64 => pure .F64 | .f128 => pure .F128 | .ppcf128 => pure .PpcF128
  | .unknown _ => throw (.unsupported "float tag")

def primitive (target : RuntimeTargetDataLayout) (source : PrimitiveLayout) : Result Primitive := do
  let expected ← size source.sizeBytes
  match source.kind with
  | .integer =>
    let kind ← require source.integerKind "primitive.integer_kind"
    let .known kind := kind | throw (.unsupported "integer tag")
    let integer ← integer kind
    if integer.size != expected then throw (.invalid "integer" "tag/size mismatch")
    return .Int integer (← require source.signed "primitive.signed")
  | .float =>
    let f ← float (← require source.floatKind "primitive.float_kind")
    if f.size != expected then throw (.invalid "float" "tag/size mismatch")
    return .Float f
  | .pointer =>
    let space : AddressSpace := ⟨← u32 (← require source.addressSpace "primitive.address_space") "address space"⟩
    let pointerSize ← (target.pointerSizeIn space).mapError (fun e => .invalid "pointer" (toString e))
    if pointerSize != expected then throw (.invalid "pointer" "target/primitive size mismatch")
    return .Pointer space
  | .unknown _ => throw (.unsupported "primitive kind")

def scalar (target : RuntimeTargetDataLayout) (source : ScalarLayout) : Result ABI.Scalar := do
  let value ← primitive target source.primitive
  match source.kind with
  | .initialized =>
    let (first,last) ← require source.validRange "scalar.valid_range"
    let range : WrappingRange := ⟨← u128 first "range.start", ← u128 last "range.end"⟩
    let width ← size source.primitive.sizeBytes
    let _ ← (range.isFullFor width).mapError (fun e => .invalid "scalar range" (reprStr e))
    return .Initialized (value := value) (validRange := range)
  | .union => return .Union (value := value)
  | .unknown _ => throw (.unsupported "scalar kind")

def backend (target : RuntimeTargetDataLayout) (source : Input.BackendRepr) : Result ABI.BackendRepr := do
  unless source.status == .supported do throw (.unsupported "backend representation status")
  match source.kind with
  | .scalar => return .Scalar (← scalar target (← require source.scalar "backend.scalar"))
  | .scalarPair =>
    let a ← scalar target (← require source.first "backend.first")
    let b ← scalar target (← require source.second "backend.second")
    return .ScalarPair (a := a) (b := b) (bOffset := ← size (← require source.secondOffsetBytes "backend.second_offset"))
  | .memory => return .Memory (sized := ← require source.sized "backend.sized")
  | .simdVector | .scalableSimdVector =>
    let element ← scalar target (← require source.element "backend.element")
    let count ← (BackendLaneCount.new (← u64 (← require source.laneCount "backend.lane_count") "lane count"))
      |>.mapError (fun e => .invalid "lane count" (reprStr e))
    if source.kind == .simdVector then return .SimdVector (element := element) (count := count)
    let vectors ← require source.vectorCount "backend.vector_count"
    if vectors == 0 || vectors > 8 then throw (.invalid "vector count" "outside 1..=8")
    return .SimdScalableVector (element := element) (count := count)
      (numberOfVectors := ⟨UInt8.ofNat vectors⟩)
  | .unknown _ => throw (.unsupported "backend kind")

def fields (source : FieldShape) : Result FieldsShape := do
  let result ← match source.kind with
    | .primitive =>
      if source.fieldCount != 0 then throw (.invalid "primitive fields" "nonzero field count")
      pure .Primitive
    | .union =>
      if (← require source.offsetBytes "union.offset_bytes") != 0 then
        throw (.invalid "union" "nonzero offset")
      pure (.Union source.fieldCount)
    | .array => pure (.Array (← size (← require source.strideBytes "array.stride"))
        (← u64 source.fieldCount "array count"))
    | .arbitrary =>
      if source.fieldCount != source.offsetsBytes.size then throw (.invalid "fields" "count mismatch")
      pure (.Arbitrary (← source.offsetsBytes.mapM size) source.memoryOrder)
    | .unknown _ => throw (.unsupported "field shape")
  result.validate.mapError (fun e => .invalid "fields" (reprStr e))
  pure result

def niche (target : RuntimeTargetDataLayout) (source : Option NicheLayout) : Result (Option Niche) := do
  let some source := source | return none
  if source.primitive.kind == .integer then
    match source.primitive.integerKind with
    | some (.known .i8) | some (.known .i16) | some (.known .i32)
    | some (.known .i64) | some (.known .i128) => pure ()
    | _ => throw (.unsupported "niche integer tag")
  let value ← primitive target source.primitive
  let range : WrappingRange := ⟨← u128 source.validRange.1 "niche.start", ← u128 source.validRange.2 "niche.end"⟩
  let width ← value.size target |>.mapError (fun e => .invalid "niche size" (toString e))
  let _ ← range.isFullFor width |>.mapError (fun e => .invalid "niche range" (reprStr e))
  return some ⟨← size source.offsetBytes, value, range⟩

def encoding (source : Input.TagEncoding) : Result ABI.TagEncoding := do
  if source.status != .supported then throw (.unsupported "tag encoding status")
  match source.kind with
  | .direct => pure .Direct
  | .niche =>
    let (first,last) ← require source.nicheVariants "tag.niche_variants"
    if first > last then throw (.invalid "niche variants" "reversed range")
    return .Niche (← require source.untaggedVariant "tag.untagged_variant") first last
      (← u128 (← require source.nicheStart "tag.niche_start") "niche start")
  | .unknown _ => throw (.unsupported "tag encoding")

private def variant (target : RuntimeTargetDataLayout) (source : Input.LayoutVariant) : Result ABI.VariantLayout := do
  let shape := source.fieldShape
  if shape.kind != .arbitrary then throw (.invalid "variant fields" "not arbitrary")
  let offsets ← source.fieldOffsetsBytes.mapM size
  let memoryOrder := shape.memoryOrder
  let rawOffsets := shape.offsetsBytes
  if rawOffsets != source.fieldOffsetsBytes then throw (.invalid "variant offsets" "duplicate metadata mismatch")
  if shape.fieldCount != offsets.size then throw (.invalid "variant fields" "count mismatch")
  (FieldsShape.Arbitrary offsets memoryOrder).validate.mapError (fun e => .invalid "variant fields" (reprStr e))
  return {
    size := ← size source.sizeBytes, backendRepr := ← backend target source.backendRepr,
    fieldOffsets := offsets, fieldsInMemoryOrder := memoryOrder,
    largestNiche := ← niche target source.largestNiche, uninhabited := source.uninhabited }

def variants (target : RuntimeTargetDataLayout) (source : VariantsLayout) : Result ABI.Variants := do
  unless source.status == .supported do throw (.unsupported "variants status")
  match source.kind with
  | .empty => pure .Empty
  | .single => return .Single (← require source.variantIndex "variant index")
  | .multiple =>
    let mut values := #[]
    for source in source.variants do
      if source.variantIndex != values.size then throw (.invalid "variants" "noncontiguous source indices")
      values := values.push (← variant target source)
    return .Multiple (← scalar target (← require source.tag "variants.tag"))
      (← encoding (← require source.tagEncoding "variants.tag_encoding"))
      (← require source.tagFieldIndex "variants.tag_field_index") values
  | .unknown _ => throw (.unsupported "variants kind")

def layout (target : RuntimeTargetDataLayout) (source : Input.Layout) : Result LayoutData := do
  if source.status != .supported || source.kind != .layout then throw (.unsupported "layout query")
  let maxAlign ← source.maxReprAlignBytes.mapM alignment
  let fields ← fields (← require source.fields "layout.fields")
  let duplicateOffsets ← source.fieldOffsetsBytes.mapM size
  if fields.count != duplicateOffsets.size then throw (.invalid "field offsets" "count mismatch")
  for index in List.range fields.count do
    let offset ← fields.offset index |>.mapError (fun e => .invalid "field offset" (reprStr e))
    if duplicateOffsets[index]? != some offset then throw (.invalid "field offsets" "mismatch")
  let variants ← variants target (← require source.variantsLayout "layout.variants")
  let uninhabited ← require source.uninhabited "layout.uninhabited"
  if variants == .Empty && !uninhabited then throw (.invalid "empty variants" "inhabited layout")
  return {
    fields, variants, backendRepr := ← backend target (← require source.backendRepresentation "layout.backend"),
    largestNiche := ← niche target source.largestNiche, uninhabited,
    align := .new (← alignment (← require source.abiAlignBytes "layout.align")),
    size := ← size (← require source.sizeBytes "layout.size"), maxReprAlign := maxAlign,
    unadjustedAbiAlign := ← alignment (← require source.unadjustedAbiAlignBytes "layout.unadjusted_align"),
    reprC := ← require source.reprC "layout.repr_c",
    randomizationSeed := ← u64 (← require source.randomizationSeed "layout.randomization_seed") "seed" }


private def pointerSpec (j : Lean.Json) : Result PointerSpec := do
  return ⟨← size (← number j "pointer_size_bytes"),
    ← alignment (← number j "pointer_align_bytes"),
    ← size (← number j "pointer_offset_bytes"), ← truth j "is_fat"⟩

/-- Every canonical target field is required. LLVM's original layout string
and address-space bounds stay in the enclosing source document as evidence. -/
def importTarget (j : Lean.Json) : Result RuntimeTargetDataLayout := do
  if (← text j "status") != "supported" then throw (.unsupported "target layout")
  let endian ← match ← text j "endian" with
    | "little" => pure Endian.little | "big" => pure .big
    | _ => throw (.unsupported "target endian")
  let width ← match ← number j "pointer_width_bits" with
    | 16 => pure PointerWidth.w16 | 32 => pure .w32 | 64 => pure .w64
    | _ => throw (.unsupported "target pointer width")
  let base : TargetDataLayout := ⟨endian, width⟩
  if (← u64 (← number j "object_size_bound_bytes") "object bound") != base.objSizeBound then
    throw (.invalid "object bound" "target arithmetic view mismatch")
  let align (name : String) := do alignment (← number j (name ++ "_align_bytes"))
  let vectors ← (← array j "vector_align").mapM fun entry => do
    pure (← size (← number entry "size_bytes"), ← alignment (← number entry "align_bytes"))
  let spaces ← (← array j "address_space_info").mapM fun entry => do
    pure (AddressSpace.mk (← u32 (← number entry "address_space") "address space"),
      ← pointerSpec (← jsonField entry "spec"))
  let cEnum ← match ← text j "c_enum_min_size" with
    | "I8" => pure Integer.I8 | "I16" => pure .I16 | "I32" => pure .I32
    | "I64" => pure .I64 | "I128" => pure .I128
    | _ => throw (.unsupported "C enum min size")
  let result : RuntimeTargetDataLayout := {
    base, i1Align := ← align "i1", i8Align := ← align "i8", i16Align := ← align "i16",
    i32Align := ← align "i32", i64Align := ← align "i64", i128Align := ← align "i128",
    f16Align := ← align "f16", f32Align := ← align "f32", f64Align := ← align "f64",
    f128Align := ← align "f128", aggregateAlign := ← align "aggregate", vectorAlign := vectors,
    defaultAddressSpace := ⟨← u32 (← number j "default_address_space") "default address space"⟩,
    defaultAddressSpacePointerSpec := ← pointerSpec (← jsonField j "default_address_space_pointer_spec"),
    addressSpaceInfo := spaces,
    instructionAddressSpace := ⟨← u32 (← number j "instruction_address_space") "instruction address space"⟩,
    cEnumMinSize := cEnum }
  result.validate.mapError (fun e => .invalid "target" (toString e))
  return result

end RuntimeMetadata

/-- Internal metadata cache. A failed type-layout conversion remains a stored
obligation; successful import never marks the document execution-ready. -/
structure RuntimeMetadata where
  source : ImportDocumentCore
  target : RuntimeTargetDataLayout
  layouts : Miri.MIR.SharedTable (Except RuntimeMetadataError LayoutData)

namespace RuntimeMetadata

/-- Thin indexed view of the same checked layout arrays. -/
structure Indexed extends RuntimeMetadata where
  private mk ::

@[inline] def Indexed.ofMetadata (metadata : RuntimeMetadata) : Indexed := ⟨metadata⟩

instance : Coe Indexed RuntimeMetadata where
  coe := Indexed.toRuntimeMetadata

def ofDocument (document : ImportDocumentCore) : Result RuntimeMetadata := do
  let source ← require document.runtimeTargetDataLayout "runtime_target_data_layout"
  let target ← source.runtime
  for (node, index) in document.types.toList.zipIdx do
    if node.id < index then throw (.duplicateType node.id)
    unless node.id == index do throw (.invalid s!"type {node.id}" "type ID does not match array index")
  let layouts := document.layoutTable.map (fun source => source.map (layout target))
  return {
    source := document
    target := target
    layouts := layouts
  }

def node (metadata : RuntimeMetadata) (id : TypeId) : Result TypeNode := do
  let value ← require metadata.source.types[id]? s!"type {id}"
  unless value.id == id do throw (.invalid s!"type {id}" "type ID does not match array index")
  return value

def lookup (metadata : RuntimeMetadata) (id : TypeId) : Result (TyAndLayout TypeId) := do
  let source ← metadata.node id
  let result ← metadata.layouts.lookup source.layoutId
    |>.mapError fun layoutId => RuntimeMetadataError.invalid s!"layout {layoutId}" "layout table entry missing"
  return ⟨id, ← result⟩

def Indexed.node (metadata : Indexed) (id : TypeId) : Result TypeNode :=
  metadata.toRuntimeMetadata.node id

def Indexed.lookup (metadata : Indexed) (id : TypeId) : Result (TyAndLayout TypeId) :=
  metadata.toRuntimeMetadata.lookup id

/-- This is an explicit diagnostic inventory, not an execution-readiness test. -/
def obligations (metadata : RuntimeMetadata) : Array (TypeId × RuntimeMetadataError) :=
  metadata.source.types.filterMap fun source => match metadata.lookup source.id with
    | .error error => some (source.id, error)
    | .ok _ => none

def findKind (metadata : RuntimeMetadata) (kind : TypeShapeKind) : Result (TyAndLayout TypeId) := do
  let nodes := metadata.source.types.filter (·.shapeKind == kind)
  if nodes.size != 1 then throw (.unsupported "ambiguous or absent type-kind lookup")
  let value ← require nodes[0]? "type kind"
  metadata.lookup value.id

/-- Canonical primitive lookup compares the compiler integer tag, rather than
choosing an arbitrary member of the broad `int`/`uint` shape category. -/
def integerLayout (metadata : RuntimeMetadata) (kind : MIR.IntegerKind) : Result (TyAndLayout TypeId) := do
  let nodes := metadata.source.types.filter fun node =>
    node.shapeMetadata.signedKind == some (.known kind) || node.shapeMetadata.unsignedKind == some (.known kind)
  unless nodes.size == 1 do throw (.unsupported "ambiguous or absent exact integer type")
  let value ← require nodes[0]? "integer type"
  metadata.lookup value.id

/-- Pinned `TyAbiInterface::ty_and_layout_field` maps every `str` field
request to `tcx.types.u8`. Older exports may have no projection row for this
special case, so recover it only from a unique, supported typed U8 node. -/
private def stringElementLayout (metadata : RuntimeMetadata) : Result (TyAndLayout TypeId) := do
  let nodes := metadata.source.types.filter fun node =>
    node.shapeKind == .uint && node.shapeStatus == .supported &&
      node.shapeMetadata.unsignedKind == some (.known .u8)
  unless nodes.size == 1 do throw (.unsupported "ambiguous or absent exact string element type")
  let value ← require nodes[0]? "string element type"
  metadata.lookup value.id

/-- Source Ty::new_tup identity from the exact ordered compiler element IDs.
No size, display spelling, or first-match heuristic establishes a tuple type. -/
def tupleLayout (metadata : RuntimeMetadata) (elements : Array TypeId) : Result (TyAndLayout TypeId) := do
  let mut candidates := #[]
  for node in metadata.source.types do
    if node.shapeKind == .tuple && node.shapeStatus == .supported then
      let id ← require node.relations.elements "tuple element list"
      let ids ← metadata.source.typeRelationTables.typeLists.lookup id |>.mapError
        (fun id => RuntimeMetadataError.invalid "tuple elements" s!"missing ID {id}")
      if ids == elements then candidates := candidates.push node.id
  unless candidates.size == 1 do throw (.unsupported "ambiguous or absent exact tuple type")
  metadata.lookup (← require candidates[0]? "tuple type")

def overflowTupleLayout (metadata : RuntimeMetadata) (element : TyAndLayout TypeId) : Result (TyAndLayout TypeId) := do
  let boolean ← metadata.findKind .bool
  metadata.tupleLayout #[element.ty,boolean.ty]

private def projectionEntry (table : Miri.MIR.SharedTable A) (id : Nat) (kind : String) : Result A :=
  table.lookup id |>.mapError fun id => RuntimeMetadataError.invalid kind s!"missing ID {id}"

def typeElements (metadata : RuntimeMetadata) (id : TypeId) : Result (Array TypeId) := do
  let node ← metadata.node id
  projectionEntry metadata.source.typeRelationTables.typeLists (← require node.relations.elements "type elements") "type elements"

def typeRepresentation (metadata : RuntimeMetadata) (id : TypeId) : Result TypeRepresentation := do
  let node ← metadata.node id
  let value ← projectionEntry metadata.source.typeRelationTables.representations
    (← require node.relations.representation "type representation") "type representation"
  unless value.status == .supported do throw (.unsupported "type representation")
  return value

def typeVariants (metadata : RuntimeMetadata) (id : TypeId) : Result (Array Nat) := do
  let node ← metadata.node id
  projectionEntry metadata.source.typeRelationTables.variantLists (← require node.relations.variants "type variants") "type variants"

def typeVariant (metadata : RuntimeMetadata) (id : TypeId) (index : Nat) : Result TypeVariant := do
  let variants ← metadata.typeVariants id
  let variant ← projectionEntry metadata.source.typeRelationTables.variants (← require variants[index]? "type variant") "type variant"
  unless variant.index == index do throw (.invalid "type variant" "index mismatch")
  return variant

def typeFields (metadata : RuntimeMetadata) (variant : TypeVariant) : Result (Array TypeField) := do
  let ids ← projectionEntry metadata.source.typeRelationTables.fieldLists variant.fields "type fields"
  ids.mapM fun id => projectionEntry metadata.source.typeRelationTables.fields id "type field"

private def projectionParents (metadata : RuntimeMetadata) (id : TypeId) : Result (Array Nat) := do
  let node ← metadata.node id
  let some facts := node.compilerFacts | return #[]
  let some queryId := facts.projectionQuery | return #[]
  let tables := metadata.source.projectionTables
  let query ← projectionEntry tables.queries queryId "projection query"
  unless query.status == .supported do throw (.unsupported "compiler projection queries")
  let some valueId := query.value | return #[]
  let value ← projectionEntry tables.values valueId "projection value"
  unless value.typingEnvironment == "fully_monomorphized" do
    throw (.invalid "projection query" "typing environment mismatch")
  projectionEntry tables.parentLists value.parents "projection parents"

private def projectionLayout (metadata : RuntimeMetadata) (id : TypeId) (layoutId : LayoutId) :
    Result (TyAndLayout TypeId) := do
  let result ← projectionEntry metadata.layouts layoutId "projection layout"
  return ⟨id, ← result⟩

/-- Source type relationships are read from typed compiler payloads, never
from display/debug strings. ADT field selection uses the selected variant. -/
def field (metadata : RuntimeMetadata) (parent : TyAndLayout TypeId) (index : Nat) :
    Result (TyAndLayout TypeId) := do
  let node ← metadata.node parent.ty
  let tables := metadata.source.projectionTables
  for recordId in ← projectionParents metadata parent.ty do
    let record ← projectionEntry tables.parents recordId "projection parent"
    let queried ← projectionLayout metadata parent.ty record.layoutId
    if queried == parent then
      let fields ← projectionEntry tables.fieldLists record.fields "projection fields"
      -- The source `str` branch ignores the requested index and always
      -- returns u8. The producer represents that single exact query result
      -- at row zero; do not infer a fictitious field count from it.
      let sourceIndex := if node.shapeKind == .str then 0 else index
      let sourceId ← require fields[sourceIndex]? "compiler projection field"
      let source ← projectionEntry tables.fields sourceId "projection field"
      unless source.index == sourceIndex do throw (.invalid "projection field" "field index mismatch")
      let _ ← metadata.node source.typeId
      return ← projectionLayout metadata source.typeId source.layoutId
  if node.shapeStatus != .supported then throw (.unsupported "type shape")
  let id ← match node.shapeKind with
    | .tuple => do
      let id ← require node.relations.elements "tuple element list"
      let values ← projectionEntry metadata.source.typeRelationTables.typeLists id "tuple elements"
      require values[index]? "tuple field"
    | .array | .slice => require node.relations.element "element type"
    | .str => return ← stringElementLayout metadata
    | .adt => do
      let .Single selected := parent.layout.variants
        | throw (.unsupported "ADT field needs selected variant")
      let tables := metadata.source.typeRelationTables
      let variants ← projectionEntry tables.variantLists (← require node.relations.variants "ADT variants") "ADT variants"
      let variant ← projectionEntry tables.variants (← require variants[selected]? "ADT variant") "ADT variant"
      unless variant.index == selected do throw (.invalid "ADT variant" "index mismatch")
      let fields ← projectionEntry tables.fieldLists variant.fields "ADT fields"
      let field ← projectionEntry tables.fields (← require fields[index]? "ADT field") "ADT field"
      unless field.index == index do throw (.invalid "ADT field" "index mismatch")
      pure field.typeId
    | _ => throw (.unsupported "type field query")
  metadata.lookup id

/-- Reconstructs precisely `LayoutData::for_variant` in pinned
rustc_abi/layout/simple.rs:158–185. Missing uninhabited-variant compiler queries
remain obligations instead of fabricated field metadata. -/
def forVariant (metadata : RuntimeMetadata) (parent : TyAndLayout TypeId) (index : Nat) :
    Result (TyAndLayout TypeId) := do
  let _ ← metadata.node parent.ty
  let tables := metadata.source.projectionTables
  let records ← projectionParents metadata parent.ty
  if let some recordId := records[index + 1]? then
    let record ← projectionEntry tables.parents recordId "projection variant"
    unless record.variant == some index do throw (.invalid "projection variant" "variant index mismatch")
    let canonical ← metadata.lookup parent.ty
    unless canonical == parent do
      match parent.layout.variants with
      | .Single actual =>
        if actual == index then return parent
        throw (.invalid "compiler variant projection" "cannot apply for_variant twice to a selected parent")
      | _ => throw (.invalid "compiler variant projection" "parent differs from exact source layout")
    return ← projectionLayout metadata parent.ty record.layoutId
  match parent.layout.variants with
  | .Single actual =>
    if actual == index then return parent
    throw (.unsupported "compiler uninhabited variant query")
  | .Empty => throw (.unsupported "compiler empty-enum variant query")
  | .Multiple _ _ _ variants =>
    let variant ← require variants[index]? "variant index"
    return ⟨parent.ty, { parent.layout with
      fields := .Arbitrary variant.fieldOffsets variant.fieldsInMemoryOrder
      variants := .Single index
      backendRepr := variant.backendRepr
      largestNiche := variant.largestNiche
      uninhabited := variant.uninhabited
      size := variant.size
      randomizationSeed := 0 }⟩

def pointee (metadata : RuntimeMetadata) (parent : TyAndLayout TypeId) :
    Result (TyAndLayout TypeId) := do
  let node ← metadata.node parent.ty
  if node.shapeStatus != .supported then throw (.unsupported "pointee shape")
  match node.shapeKind with
  | .rawPointer | .reference =>
    metadata.lookup (← require node.relations.pointee "pointee type")
  | _ => throw (.unsupported "non-pointer pointee query")

/-- Boundary adapter preserves missing compiler metadata as explicit failures. -/
def queries (metadata : RuntimeMetadata) : LayoutQueries TypeId := {
  field := fun parent index => (metadata.field parent index).mapError (fun _ => .missingField index)
  variant := fun parent index => (metadata.forVariant parent index).mapError (fun _ => .missingVariant index)
  pointee := fun parent => (metadata.pointee parent).mapError (fun _ => .missingPointee) }

end RuntimeMetadata
end Miri.Input
