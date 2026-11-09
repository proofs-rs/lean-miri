import Miri.Input.Model
import Miri.Input.Decoder
import Miri.ABI.Layout

/-! Internal compiler-metadata bridge, not the public import API. Successful
conversion supplies records and queries; it does not establish execution
readiness, machine-hook adequacy, or Rust UB freedom. Original source nodes
remain available beside every canonical layout result. -/
namespace Miri.Input
open Miri.ABI

inductive RuntimeMetadataError where
  | missing (path : String)
  | unsupported (path : String)
  | invalid (path message : String)
  | duplicateType (id : TypeId)
  | unknownType (id : TypeId)
  deriving DecidableEq, Repr
instance : ToString RuntimeMetadataError where
  toString e := reprStr e

namespace RuntimeMetadata

/-- A private, checked certificate that one immutable JSON tree compares equal
to itself. JSON's `BEq` is not assumed lawful: a malformed tree may fail this
test, in which case comparisons must retain their ordinary recursive path. -/
structure JsonReflexivity (left : Lean.Json) where
  private mk ::
  reflexive : Option (PLift ((left == left) = true))

namespace JsonReflexivity

def prepare {left : Lean.Json} : JsonReflexivity left :=
  ⟨if h : left == left then some ⟨h⟩ else none⟩

/-- Compare in the source-left orientation, preserving `left == candidate`. -/
def matchesRight {left : Lean.Json} (certificate : JsonReflexivity left) (candidate : Lean.Json) : Bool :=
  match certificate.reflexive with
  | none => left == candidate
  | some ⟨reflexive⟩ =>
      withPtrEq left candidate (fun _ => left == candidate)
        (by intro equal; cases equal; exact reflexive)

/-- Compare in the candidate-left orientation, preserving `candidate == left`. -/
def matchesLeft {left : Lean.Json} (certificate : JsonReflexivity left) (candidate : Lean.Json) : Bool :=
  match certificate.reflexive with
  | none => candidate == left
  | some ⟨reflexive⟩ =>
      withPtrEq candidate left (fun _ => candidate == left)
        (by intro equal; cases equal; exact reflexive)

/-- Reuse a supplied source-equality proof; otherwise compare the source value. -/
def matchesRightOr {left : Lean.Json} (certificate : Option (JsonReflexivity left)) (candidate : Lean.Json) : Bool :=
  match certificate with
  | none => left == candidate
  | some certificate => certificate.matchesRight candidate

theorem matchesRight_eq {left : Lean.Json} (certificate : JsonReflexivity left) (candidate : Lean.Json) :
    certificate.matchesRight candidate = (left == candidate) := by
  cases h : certificate.reflexive <;>
    simp [matchesRight, h, withPtrEq]

theorem matchesLeft_eq {left : Lean.Json} (certificate : JsonReflexivity left) (candidate : Lean.Json) :
    certificate.matchesLeft candidate = (candidate == left) := by
  cases h : certificate.reflexive <;>
    simp [matchesLeft, h, withPtrEq]

theorem matchesRightOr_eq {left : Lean.Json} (certificate : Option (JsonReflexivity left)) (candidate : Lean.Json) :
    matchesRightOr certificate candidate = (left == candidate) := by
  cases certificate with
  | none => rfl
  | some certificate => exact certificate.matchesRight_eq candidate

end JsonReflexivity
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

def primitive (target : RuntimeTargetDataLayout) (source : PrimitiveLayout) : Result Primitive := do
  let expected ← size source.sizeBytes
  match source.kind with
  | .integer =>
    let kind ← require source.integerKind "primitive.integer_kind"
    let .known kind := kind
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

def backend (target : RuntimeTargetDataLayout) (source : Input.BackendRepr) : Result ABI.BackendRepr := do
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
  result.validate.mapError (fun e => .invalid "fields" (reprStr e))
  pure result

def niche (target : RuntimeTargetDataLayout) (source : Option NicheLayout) : Result (Option Niche) := do
  let some source := source | return none
  let value ← primitive target source.primitive
  let range : WrappingRange := ⟨← u128 source.validRange.1 "niche.start", ← u128 source.validRange.2 "niche.end"⟩
  let width ← value.size target |>.mapError (fun e => .invalid "niche size" (toString e))
  let _ ← range.isFullFor width |>.mapError (fun e => .invalid "niche range" (reprStr e))
  return some ⟨← size source.offsetBytes, value, range⟩

def encoding (source : Input.TagEncoding) : Result ABI.TagEncoding := do
  match source.kind with
  | .direct => pure .Direct
  | .niche =>
    let (first,last) ← require source.nicheVariants "tag.niche_variants"
    if first > last then throw (.invalid "niche variants" "reversed range")
    return .Niche (← require source.untaggedVariant "tag.untagged_variant") first last
      (← u128 (← require source.nicheStart "tag.niche_start") "niche start")

private def variant (target : RuntimeTargetDataLayout) (source : Input.LayoutVariant) : Result ABI.VariantLayout := do
  if source.fields.kind != .arbitrary then throw (.invalid "variant fields" "not arbitrary")
  let offsets ← source.fieldOffsetsBytes.mapM size
  let memoryOrder := source.fields.memoryOrder
  if source.fields.offsetsBytes != source.fieldOffsetsBytes then throw (.invalid "variant offsets" "duplicate metadata mismatch")
  if source.fields.fieldCount != offsets.size then throw (.invalid "variant fields" "count mismatch")
  (FieldsShape.Arbitrary offsets memoryOrder).validate.mapError (fun e => .invalid "variant fields" (reprStr e))
  return {
    size := ← size source.sizeBytes, backendRepr := ← backend target source.backendRepr,
    fieldOffsets := offsets, fieldsInMemoryOrder := memoryOrder,
    largestNiche := ← niche target source.largestNiche, uninhabited := source.uninhabited }

def variants (target : RuntimeTargetDataLayout) (source : VariantsLayout) : Result ABI.Variants := do
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

def layout (target : RuntimeTargetDataLayout) (source : Input.Layout) : Result LayoutData := do
  let maxAlign ← source.maxReprAlignBytes.mapM alignment
  let fields ← fields (← require source.fields "layout.fields")
  let duplicateOffsets ← source.fieldOffsetsBytes.mapM size
  if fields.count != duplicateOffsets.size then throw (.invalid "field offsets" "count mismatch")
  for index in List.range fields.count do
    let offset ← fields.offset index |>.mapError (fun e => .invalid "field offset" (reprStr e))
    if duplicateOffsets[index]? != some offset then throw (.invalid "field offsets" "mismatch")
  let variants ← variants target (← require source.variantsLayout "layout.variants")
  let uninhabited := source.uninhabited
  if variants == .Empty && !uninhabited then throw (.invalid "empty variants" "inhabited layout")
  return {
    fields, variants, backendRepr := ← backend target (← require source.backendRepresentation "layout.backend"),
    largestNiche := ← niche target source.largestNiche, uninhabited,
    align := .new (← alignment (← require source.abiAlignBytes "layout.align")),
    size := ← size (← require source.sizeBytes "layout.size"), maxReprAlign := maxAlign,
    unadjustedAbiAlign := ← alignment (← require source.unadjustedAbiAlignBytes "layout.unadjusted_align"),
    reprC := source.reprC, randomizationSeed := ← u64 source.randomizationSeed "seed" }


private def pointerSpec (j : Lean.Json) : Result PointerSpec := do
  return ⟨← size (← number j "pointer_size_bytes"),
    ← alignment (← number j "pointer_align_bytes"),
    ← size (← number j "pointer_offset_bytes"), ← truth j "is_fat"⟩

/-- Every canonical target field is required. LLVM's original layout string
and address-space bounds stay in the enclosing source document as evidence. -/
def importTarget (j : Lean.Json) : Result RuntimeTargetDataLayout := do
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

/-- Immutable compiler tables and target semantics. ID lookup directly indexes
validated dense tables; semantic layouts are constructed only on demand. -/
structure RuntimeMetadata where
  source : ImportDocument
  target : RuntimeTargetDataLayout

namespace RuntimeMetadata

/-- Source binding is a proof about the owned input, not an ID lookup cache. -/
structure Indexed extends RuntimeMetadata where
  rawReflexivity : JsonReflexivity source.raw

def Indexed.ofMetadata (metadata : RuntimeMetadata)
    (sourceEquality : Option (JsonReflexivity metadata.source.raw) := none) : Indexed :=
  { toRuntimeMetadata := metadata
    rawReflexivity := sourceEquality.getD (JsonReflexivity.prepare (left := metadata.source.raw)) }

/-- Compare a candidate document using the exact original JSON equality. The
checked self-equality certificate permits Lean's safe `withPtrEq` fast path
when the indexed metadata object is reused by the source world. -/
def Indexed.matchesSourceLeft (metadata : Indexed) (left : Lean.Json) : Bool :=
  metadata.rawReflexivity.matchesLeft left

theorem Indexed.matchesSourceLeft_eq (metadata : Indexed) (left : Lean.Json) :
    metadata.matchesSourceLeft left = (left == metadata.source.raw) := by
  simpa [Indexed.matchesSourceLeft] using metadata.rawReflexivity.matchesLeft_eq left

instance : Coe Indexed RuntimeMetadata where
  coe := Indexed.toRuntimeMetadata

def ofDocument (document : ImportDocument) : Result RuntimeMetadata := do
  let target ← importTarget (← jsonField document.raw "runtime_target_data_layout")
  let mut seen : Std.HashSet TypeId := {}
  for node in document.types do
    if seen.contains node.id then throw (.duplicateType node.id)
    seen := seen.insert node.id
  return {
    source := document
    target := target
  }

def node (metadata : RuntimeMetadata) (id : TypeId) : Result TypeNode := do
  let value ← require metadata.source.types[id]? s!"type {id}"
  unless value.id == id do throw (.invalid "compiler type ID" "row/index mismatch")
  pure value

def lookup (metadata : RuntimeMetadata) (id : TypeId) : Result (TyAndLayout TypeId) := do
  let sourceNode ← metadata.node id
  let sourceLayout ← require metadata.source.layouts[sourceNode.layoutId]?
    s!"compiler layout ID {sourceNode.layoutId} out of bounds"
  return ⟨id,← layout metadata.target sourceLayout⟩

def Indexed.node (metadata : Indexed) (id : TypeId) : Result TypeNode :=
  metadata.toRuntimeMetadata.node id

def Indexed.lookup (metadata : Indexed) (id : TypeId) : Result (TyAndLayout TypeId) :=
  metadata.toRuntimeMetadata.lookup id

/-- This is an explicit diagnostic inventory, not an execution-readiness test. -/
def obligations (metadata : RuntimeMetadata) : Array (TypeId × RuntimeMetadataError) :=
  metadata.source.types.filterMap fun node => match metadata.lookup node.id with
    | .error e => some (node.id,e) | .ok _ => none

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
request to `tcx.types.u8`. The source query ignores the field index; a unique
canonical U8 identity supplies its exact type and layout. -/
private def stringElementLayout (metadata : RuntimeMetadata) : Result (TyAndLayout TypeId) := do
  let nodes := metadata.source.types.filter fun node =>
    node.shapeKind == .uint &&
      node.shapeMetadata.unsignedKind == some (.known .u8)
  unless nodes.size == 1 do throw (.unsupported "ambiguous or absent exact string element type")
  let value ← require nodes[0]? "string element type"
  metadata.lookup value.id

/-- Source Ty::new_tup identity from the exact ordered compiler element IDs.
No size, display spelling, or first-match heuristic establishes a tuple type. -/
def tupleLayout (metadata : RuntimeMetadata) (elements : Array TypeId) : Result (TyAndLayout TypeId) := do
  let mut candidates := #[]
  for node in metadata.source.types do
    if node.shapeKind == .tuple then
      let .tuple ids := node.shape | throw (.invalid "tuple type" "shape mismatch")
      if ids == elements then candidates := candidates.push node.id
  unless candidates.size == 1 do throw (.unsupported "ambiguous or absent exact tuple type")
  metadata.lookup (← require candidates[0]? "tuple type")

def overflowTupleLayout (metadata : RuntimeMetadata) (element : TyAndLayout TypeId) : Result (TyAndLayout TypeId) := do
  let boolean ← metadata.findKind .bool
  metadata.tupleLayout #[element.ty,boolean.ty]

private def typeRef (source : Lean.Json) : Result TypeId := convert "compiler type ID" source.getNat?

private def projectionParents (metadata : RuntimeMetadata) (id : TypeId) : Result (Array ProjectionParent) := do
  let node ← metadata.node id
  let some facts := node.compilerFacts | return #[]
  let some queries := facts.projectionQueries | return #[]
  unless queries.typingEnvironment == "fully_monomorphized" do
    throw (.invalid "projection query" "typing environment mismatch")
  pure queries.parents
/-- Resolve a physical compiler layout only at the operation that needs it. -/
def layoutById (metadata : RuntimeMetadata) (id : Nat) : Result LayoutData := do
  let source ← require metadata.source.layouts[id]? s!"compiler layout ID {id} out of bounds"
  layout metadata.target source

private def projectionLayout (metadata : RuntimeMetadata) (id : TypeId) (layoutId : LayoutId) :
    Result (TyAndLayout TypeId) := do
  return ⟨id,← metadata.layoutById layoutId⟩

/-- Source type relationships are read from typed compiler payloads, never
from display/debug strings. ADT field selection uses the selected variant. -/
def field (metadata : RuntimeMetadata) (parent : TyAndLayout TypeId) (index : Nat) :
    Result (TyAndLayout TypeId) := do
  let node ← metadata.node parent.ty
  for record in ← projectionParents metadata parent.ty do
    let queried ← projectionLayout metadata parent.ty record.layoutId
    if queried == parent then
      -- The source `str` branch ignores the requested index and always
      -- returns u8. The producer represents that single exact query result
      -- at row zero; do not infer a fictitious field count from it.
      let sourceIndex := if node.shapeKind == .str then 0 else index
      let source ← require (record.fields.find? (·.index == sourceIndex)) "compiler projection field"
      let id := source.typeId
      let _ ← metadata.node id
      return ← projectionLayout metadata id source.layoutId
  let id ← match node.shape with
    | .tuple values => require values[index]? "tuple field"
    | .array element .. | .slice element => pure element
    | .str => return ← stringElementLayout metadata
    | .adt data => do
      let .Single selected := parent.layout.variants
        | throw (.unsupported "ADT field needs selected variant")
      let variant ← require (data.variants.find? (·.index == selected)) "ADT variant"
      let source ← require (variant.fields.find? (·.index == index)) "ADT field"
      pure source.typeId
    | _ => throw (.unsupported "type field query")
  metadata.lookup id

/-- Reconstructs precisely `LayoutData::for_variant` in pinned
rustc_abi/layout/simple.rs:158–185. Missing uninhabited-variant compiler queries
remain obligations instead of fabricated field metadata. -/
def forVariant (metadata : RuntimeMetadata) (parent : TyAndLayout TypeId) (index : Nat) :
    Result (TyAndLayout TypeId) := do
  let _ ← metadata.node parent.ty
  for record in ← projectionParents metadata parent.ty do
    if record.variant == some index then
      -- Validate the supplied parent against a source default/variant result
      -- before applying another query; structural resemblance is not a key.
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
  match node.shape with
  | .rawPointer pointee _ | .reference pointee .. => metadata.lookup pointee
  | _ => throw (.unsupported "non-pointer pointee query")

/-- Boundary adapter preserves missing compiler metadata as explicit failures. -/
def queries (metadata : RuntimeMetadata) : LayoutQueries TypeId := {
  field := fun parent index => (metadata.field parent index).mapError (fun _ => .missingField index)
  variant := fun parent index => (metadata.forVariant parent index).mapError (fun _ => .missingVariant index)
  pointee := fun parent => (metadata.pointee parent).mapError (fun _ => .missingPointee) }

end RuntimeMetadata
end Miri.Input
