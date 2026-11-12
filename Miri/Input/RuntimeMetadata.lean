import Miri.Input.Model
import Miri.Input.TypeArena
import Miri.Input.StructuralNormalization
import Miri.Input.StructuralPointerMetadata
import Miri.ABI.Layout
import Miri.ABI.PrimitiveLayout
import Miri.ABI.UnivariantLayout
import Miri.ABI.StructLayout
import Miri.Input.StructLayoutMaterial
import Miri.ABI.UnionLayout

/-! Internal compiler-metadata bridge, not the public import API. Successful
conversion supplies records and queries; it does not establish execution
readiness, machine-hook adequacy, or Rust UB freedom. Compiler adapters and
runtime metadata must come from the same export: pool IDs are compilation-local.
Original source nodes remain available beside every canonical layout result. -/
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

abbrev Result := Except RuntimeMetadataError

def require (value : Option A) (path : String) : Result A :=
  match value with | some value => pure value | none => throw (.missing path)
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
  if source.tupleType.isSome || source.unionType.isSome || source.structType.isSome then
    throw (.missing "structural layout requires source type and layout pools")
  if let some recipe := source.primitiveRecipe then
    return ← PrimitiveLayout.compute target recipe
      |>.mapError (fun reason => .invalid "primitive layout recipe" reason)
  let maxAlign ← source.maxReprAlignBytes.mapM alignment
  let fields ← fields (← require source.fields "layout.fields")
  source.fieldOffsetsBytes.validate (← require source.fields "layout.fields")
    |>.mapError (fun message => .invalid "field offsets" message)
  match source.fieldOffsetsBytes with
  | .explicit offsets =>
    let duplicateOffsets ← offsets.mapM size
    for index in List.range fields.count do
      let offset ← fields.offset index |>.mapError (fun e => .invalid "field offset" (reprStr e))
      if duplicateOffsets[index]? != some offset then throw (.invalid "field offsets" "mismatch")
  | .arrayFormula _ _ => pure ()
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


private def pointerSpec (source : TargetPointerSpec) : Result PointerSpec := do
  return ⟨← size source.pointerSizeBytes, ← alignment source.pointerAlignBytes,
    ← size source.pointerOffsetBytes, source.isFat⟩

def importTarget (source : TargetDataLayoutEvidence) : Result RuntimeTargetDataLayout := do
  let endian ← match source.endian with
    | "little" => pure Endian.little | "big" => pure .big
    | _ => throw (.unsupported "target endian")
  let width ← match source.pointerWidthBits with
    | 16 => pure PointerWidth.w16 | 32 => pure .w32 | 64 => pure .w64
    | _ => throw (.unsupported "target pointer width")
  let base : TargetDataLayout := ⟨endian, width⟩
  let objectBound ← require source.objectSizeBoundBytes "object bound"
  if (← u64 objectBound "object bound") != base.objSizeBound then
    throw (.invalid "object bound" "target arithmetic view mismatch")
  let vectors ← source.vectorAlign.mapM fun (width, align) => do
    pure (← size width, ← alignment align)
  let spaces ← source.addressSpaceInfo.mapM fun entry => do
    pure (AddressSpace.mk (← u32 entry.addressSpace "address space"),
      ← pointerSpec entry.spec)
  let cEnum ← match source.cEnumMinSize with
    | "I8" => pure Integer.I8 | "I16" => pure .I16 | "I32" => pure .I32
    | "I64" => pure .I64 | "I128" => pure .I128
    | _ => throw (.unsupported "C enum min size")
  let result : RuntimeTargetDataLayout := {
    base, i1Align := ← alignment source.i1AlignBytes,
    i8Align := ← alignment source.i8AlignBytes,
    i16Align := ← alignment source.i16AlignBytes,
    i32Align := ← alignment source.i32AlignBytes,
    i64Align := ← alignment source.i64AlignBytes,
    i128Align := ← alignment source.i128AlignBytes,
    f16Align := ← alignment source.f16AlignBytes,
    f32Align := ← alignment source.f32AlignBytes,
    f64Align := ← alignment source.f64AlignBytes,
    f128Align := ← alignment source.f128AlignBytes,
    aggregateAlign := ← alignment source.aggregateAlignBytes,
    vectorAlign := vectors,
    defaultAddressSpace := ⟨← u32 source.defaultAddressSpace "default address space"⟩,
    defaultAddressSpacePointerSpec := ← pointerSpec source.defaultAddressSpacePointerSpec,
    addressSpaceInfo := spaces,
    instructionAddressSpace := ⟨← u32 source.instructionAddressSpace "instruction address space"⟩,
    cEnumMinSize := cEnum }
  result.validate.mapError (fun e => .invalid "target" (toString e))
  return result

/-- Source-aware physical layout construction. Recursive tuple recipes follow
raw source type edges; cyclic or malformed material never supplies a layout. -/
def resolveLayoutWithFuel (target : RuntimeTargetDataLayout) (types : Array TypeNode)
    (layouts : Array Input.Layout) (definitions : Array DefinitionId) : Nat → LayoutId → Result LayoutData
  | 0, _ => .error (.unsupported "material layout recipe recursion exhausted")
  | fuel + 1, id => do
    let source ← require layouts[id]? s!"compiler layout ID {id} out of bounds"
    if let some typeId := source.structType then
      unless source.primitiveRecipe.isNone && source.tupleType.isNone && source.unionType.isNone do
        throw (.invalid "struct layout recipe" "conflicting layout constructor")
      let node ← require types[typeId]? "struct recipe type ID out of bounds"
      unless node.id == typeId do throw (.invalid "struct recipe type" "row/index mismatch")
      let .adt data := node.shape
        | throw (.invalid "struct layout recipe" "source type is not an ADT")
      unless data.kind == .structKind && data.variants.size == 1 do
        throw (.invalid "struct layout recipe" "source type is not a one-variant struct")
      let definition ← require definitions[data.definition]? "struct declaration definition missing"
      let declaration ← require definition.adtDeclaration "struct raw ADT declaration missing"
      let template ← require definition.genericTemplate "struct raw field declaration missing"
      declaration.validate template |>.mapError (fun e => .invalid "struct declaration" e)
      unless declaration.kind == .structKind do
        throw (.invalid "struct declaration" "source declaration is not a struct")
      unless declaration.langItem != some "f16b" && declaration.langItem != some "ppcf128" do
        throw (.unsupported "special floating-point struct layout recipe")
      if let some tail := template.fields.back? then
        unless StructLayoutMaterial.guaranteedSized (StructLayoutMaterial.termFuel tail.expression + 1) tail.expression do
          throw (.unsupported "struct declaration tail requires ParamEnv sizedness solver")
      let variant ← require data.variants[0]? "struct material variant missing"
      unless variant.fields.size == template.fields.size do
        throw (.invalid "struct declaration" "instantiated and declared field domains differ")
      let fields ← variant.fields.mapM fun field => do
        let node ← require types[field.typeId]? "struct field type ID out of bounds"
        unless node.id == field.typeId do throw (.invalid "struct field type" "row/index mismatch")
        resolveLayoutWithFuel target types layouts definitions fuel node.layoutId
      let repr := data.representation
      unless repr.flagsBits < 256 do throw (.invalid "struct representation" "flags overflow u8")
      unless repr.flagsBits &&& (2 + 64) == 0 do
        throw (.unsupported "SIMD/scalable struct layout recipe")
      let representation : UnivariantLayout.Representation := {
        flags := UInt8.ofNat repr.flagsBits, integerRepresentation := repr.integer.isSome,
        align := ← repr.alignBytes.mapM alignment, pack := ← repr.packBytes.mapM alignment,
        fieldShuffleSeed := ← u64 repr.fieldShuffleSeed "struct field shuffle seed" }
      let niches := if declaration.langItem == some "unsafe_cell" ||
          declaration.langItem == some "unsafe_pinned" then
        StructLayout.NicheOptimizations.disabled else .enabled
      return ← StructLayout.compute target fields representation 0 false true niches
        |>.mapError (fun reason => .invalid "struct layout recipe" reason)
    if let some typeId := source.unionType then
      unless source.primitiveRecipe.isNone && source.tupleType.isNone do
        throw (.invalid "union layout recipe" "conflicting layout constructor")
      let node ← require types[typeId]? "union recipe type ID out of bounds"
      unless node.id == typeId do throw (.invalid "union recipe type" "row/index mismatch")
      let .adt data := node.shape
        | throw (.invalid "union layout recipe" "source type is not an ADT")
      unless data.kind == .unionKind && data.variants.size == 1 do
        throw (.invalid "union layout recipe" "source type is not a one-variant union")
      let variant ← require data.variants[0]? "union material variant missing"
      let fields ← variant.fields.mapM fun field => do
        let node ← require types[field.typeId]? "union field type ID out of bounds"
        unless node.id == field.typeId do throw (.invalid "union field type" "row/index mismatch")
        resolveLayoutWithFuel target types layouts definitions fuel node.layoutId
      let repr := data.representation
      unless repr.flagsBits < 256 do throw (.invalid "union representation" "flags overflow u8")
      let representation : UnivariantLayout.Representation := {
        flags := UInt8.ofNat repr.flagsBits, integerRepresentation := repr.integer.isSome,
        align := ← repr.alignBytes.mapM alignment, pack := ← repr.packBytes.mapM alignment,
        fieldShuffleSeed := ← u64 repr.fieldShuffleSeed "union field shuffle seed" }
      return ← UnionLayout.compute target fields representation
        |>.mapError (fun reason => .invalid "union layout recipe" reason)
    if let some typeId := source.tupleType then
      unless source.primitiveRecipe.isNone do
        throw (.invalid "tuple layout recipe" "conflicting primitive constructor")
      let node ← require types[typeId]? "tuple recipe type ID out of bounds"
      unless node.id == typeId do throw (.invalid "tuple recipe type" "row/index mismatch")
      let .tuple elements := node.shape
        | throw (.invalid "tuple layout recipe" "source type is not a tuple")
      let fields ← elements.mapM fun element => do
        let node ← require types[element]? "tuple element type ID out of bounds"
        unless node.id == element do throw (.invalid "tuple element type" "row/index mismatch")
        resolveLayoutWithFuel target types layouts definitions fuel node.layoutId
      let kind := if elements.isEmpty then UnivariantLayout.Kind.alwaysSized else .maybeUnsized
      return ← UnivariantLayout.compute target fields {} kind
        |>.mapError (fun reason => .invalid "tuple layout recipe" reason)
    layout target source

def resolveLayout (target : RuntimeTargetDataLayout) (types : Array TypeNode)
    (layouts : Array Input.Layout) (id : LayoutId) (definitions : Array DefinitionId) : Result LayoutData :=
  resolveLayoutWithFuel target types layouts definitions (types.size + layouts.size + 1) id

end RuntimeMetadata

/-- Immutable compiler tables and target semantics. ID lookup directly indexes
validated dense tables; semantic layouts are constructed only on demand. -/
structure RuntimeMetadata where
  source : ImportDocument
  target : RuntimeTargetDataLayout
  /-- Checked once at import. Dependence on the exact source prevents retaining
  this certificate when replacing its type table. It carries no runtime cache. -/
  denseTypes : Option (PLift (TypeArena.isDense source.types = true)) := none

namespace RuntimeMetadata

def ofDocument (document : ImportDocument) : Result RuntimeMetadata := do
  let target ← importTarget (← require document.runtimeTargetDataLayout "runtime_target_data_layout")
  let mut seen : Std.HashSet TypeId := {}
  for node in document.types do
    if seen.contains node.id then throw (.duplicateType node.id)
    seen := seen.insert node.id
  if dense : TypeArena.isDense document.types = true then
    return { source := document, target, denseTypes := some ⟨dense⟩ }
  else throw (.invalid "compiler type ID" "material type IDs are not dense row positions")

def node (metadata : RuntimeMetadata) (id : TypeId) : Result TypeNode :=
  let resolved := match metadata.denseTypes with
    | some _ => TypeArena.nodeWithFuel metadata.source.types
        metadata.source.typeConstants.size (id + 1) id
    | none => TypeArena.node metadata.source.types id metadata.source.typeConstants.size
  resolved.mapError (.invalid "type arena")

/-- Pinned pointer metadata selection from normalized type structure. Only the
DynMetadata<Self> constructor remains residual material, keyed by the exact dyn
tail; sized/extern/str/slice decisions do not inspect physical layout results. -/
def pointerMetadataType (metadata : RuntimeMetadata) (id : TypeId) : Result TypeId := do
  let lookup := fun ty => (metadata.node ty).mapError toString
  let fuel := id + metadata.source.types.size + 1
  let normalize := StructuralNormalization.normalize lookup metadata.source fuel
  let choice ← (StructuralPointerMetadata.query (fun ty => return (← lookup ty).shape)
    normalize fuel id).mapError (fun e => .unsupported s!"pointer metadata: {e}")
  let result ← match choice with
    | .unit => do
      let id := metadata.source.queries.primitives.unit
      let value ← metadata.node id
      unless (match value.shape with | .tuple fields => fields.isEmpty | _ => false) do
        throw (.invalid "pointer metadata" "unit primitive is not the empty tuple")
      pure id
    | .usize => do
      let id := metadata.source.queries.primitives.usize
      let value ← metadata.node id
      unless value.shapeMetadata.unsignedKind == some (.known .usize) do
        throw (.invalid "pointer metadata" "usize primitive has wrong integer kind")
      pure id
    | .dynamic tail => do
      let value ← metadata.node tail
      let facts ← require value.compilerFacts "dynamic pointer metadata constructor material"
      unless facts.typingEnvironment == "fully_monomorphized" do
        throw (.invalid "pointer metadata" "typing environment mismatch")
      let some (_,some result) := facts.typeQueries.find? (·.1 == "pointer_metadata_type")
        | throw (.unsupported "DynMetadata<Self> constructor material absent")
      pure result
    | .unresolved _ => throw (.unsupported "pointer metadata has unresolved alias tail")
  let _ ← metadata.node result
  pure result

private def lookupWithFuel (metadata : RuntimeMetadata) : Nat → TypeId → Result (TyAndLayout TypeId)
  | 0, _ => .error (.unsupported "lazy type layout recursion exhausted")
  | fuel + 1, id => do
    let sourceNode ← metadata.node id
    if id < metadata.source.types.size then
      return ⟨id,← resolveLayoutWithFuel metadata.target metadata.source.types
        metadata.source.layouts metadata.source.definitions (fuel + 1) sourceNode.layoutId⟩
    if let .array element _ constructor := sourceNode.shape then
      unless constructor.count < 2^(metadata.target.base.pointerWidth.bits.toNat) do
        throw (.unsupported "lazy array length overflows target usize")
      let elementLayout ← lookupWithFuel metadata fuel element
      unless elementLayout.layout.isSized do throw (.unsupported "lazy array element is unsized")
      let arrayLayout ← (PrimitiveLayout.arrayLike metadata.target elementLayout.layout
          (UInt64.ofNat constructor.count)).mapError (fun e => .unsupported e)
      return ⟨id, arrayLayout⟩
    let (pointee, isReference) ← match sourceNode.shape with
      | .rawPointer pointee .Mut => pure (pointee, false)
      | .reference pointee .Mut .Erased => pure (pointee, true)
      | _ => throw (.invalid "lazy type arena" "unsupported constructor")
    let metadataType ← metadata.pointerMetadataType pointee
    let pointerMetadata := some (← lookupWithFuel metadata fuel metadataType).layout
    let pointerLayout ← (PrimitiveLayout.pointer metadata.target isReference pointerMetadata)
      |>.mapError (fun e => .unsupported s!"lazy pointer layout: {reprStr e}")
    return ⟨id, pointerLayout⟩

def lookup (metadata : RuntimeMetadata) (id : TypeId) : Result (TyAndLayout TypeId) :=
  lookupWithFuel metadata (id + metadata.source.types.size + 1) id

/-- Synthetic array lengths inhabit a disjoint constant namespace and retain the
exact target-usize ValTree representation. Imported generic constants stay intact. -/
def typeConstant (metadata : RuntimeMetadata) (id : TypeConstantId) : Result MIR.TypeConst := do
  if let some value := metadata.source.typeConstants[id]? then return value
  let count := id - metadata.source.typeConstants.size
  let bits := metadata.target.base.pointerWidth.bits.toNat
  unless count < 2^bits do throw (.unsupported "lazy array length overflows target usize")
  let usizeType := metadata.source.queries.primitives.usize
  let value ← metadata.node usizeType
  unless value.shapeMetadata.unsignedKind == some (.known .usize) do
    throw (.invalid "lazy usize constant" "primitive is not usize")
  return .Value usizeType ⟨#[.Leaf count (bits / 8)], 0⟩

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

private def projectionParents (metadata : RuntimeMetadata) (id : TypeId) : Result (Array ProjectionParent) := do
  let node ← metadata.node id
  let some facts := node.compilerFacts | return #[]
  let some queries := facts.projectionQueries | return #[]
  unless queries.typingEnvironment == "fully_monomorphized" do
    throw (.invalid "projection query" "typing environment mismatch")
  pure queries.parents
/-- Resolve a physical compiler layout only at the operation that needs it. -/
def layoutById (metadata : RuntimeMetadata) (id : Nat) : Result LayoutData := do
  resolveLayout metadata.target metadata.source.types metadata.source.layouts id metadata.source.definitions

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
