import Miri.Input.Model
import Miri.ABI.Layout
import Miri.Input.ConcreteTypeLayout

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
  | .x87f80 => pure .X87F80
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
    x87F80Align := ← source.x87F80AlignBytes.mapM alignment,
    aggregateAlign := ← alignment source.aggregateAlignBytes,
    vectorAlign := vectors,
    defaultAddressSpace := ⟨← u32 source.defaultAddressSpace "default address space"⟩,
    defaultAddressSpacePointerSpec := ← pointerSpec source.defaultAddressSpacePointerSpec,
    addressSpaceInfo := spaces,
    instructionAddressSpace := ⟨← u32 source.instructionAddressSpace "instruction address space"⟩,
    cEnumMinSize := cEnum }
  result.validate.mapError (fun e => .invalid "target" (toString e))
  return result

end RuntimeMetadata

private def calculateLayout (source : ImportDocument) (target : RuntimeTargetDataLayout)
    (id : TypeId) : RuntimeMetadata.Result (TyAndLayout TypeId) := do
  let node ← RuntimeMetadata.require source.types[id]? s!"type {id}"
  unless node.id == id do throw (.invalid "compiler type ID" "row/index mismatch")
  let normalized := node.sourceLayout.normalizedType
  let value ← ConcreteTypeLayout.calculate source target normalized
    |>.mapError (fun message => .invalid s!"concrete layout for type {id}" message)
  return ⟨normalized, value⟩

/-- Immutable compiler tables and target semantics. ID lookup directly indexes
validated dense tables; semantic layouts are constructed only on demand. -/
structure RuntimeMetadata where
  source : ImportDocument
  target : RuntimeTargetDataLayout
  private layoutQuery : TypeId → RuntimeMetadata.Result (TyAndLayout TypeId) :=
    calculateLayout source target
  private layoutQuery_eq : ∀ id, layoutQuery id = calculateLayout source target id := by
    intro id; rfl

namespace RuntimeMetadata

def ofDocument (document : ImportDocument) : Result RuntimeMetadata := do
  let target ← importTarget (← require document.runtimeTargetDataLayout "runtime_target_data_layout")
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

def lookup (metadata : RuntimeMetadata) (id : TypeId) : Result (TyAndLayout TypeId) :=
  metadata.layoutQuery id

/-- A fresh table belongs to one invocation, even when validated materials are reused. -/
@[noinline] def startSession (metadata : RuntimeMetadata) : RuntimeMetadata :=
  let slots := Array.ofFn fun (id : Fin metadata.source.types.size) =>
    Thunk.mk fun _ => calculateLayout metadata.source metadata.target id.val
  { source := metadata.source, target := metadata.target
    layoutQuery := fun id =>
      if h : id < metadata.source.types.size then (slots[id]'(by simpa [slots] using h)).get
      else calculateLayout metadata.source metadata.target id
    layoutQuery_eq := by
      intro id
      split <;> simp_all [slots, Thunk.get] }

theorem startSession_lookup (metadata : RuntimeMetadata) (id : TypeId) :
    metadata.startSession.lookup id = metadata.lookup id := by
  exact (metadata.startSession.layoutQuery_eq id).trans (metadata.layoutQuery_eq id).symm

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

private def primitiveType (metadata : RuntimeMetadata) (primitive : Primitive) : Result TypeId := do
  let candidates := metadata.source.types.filter fun node =>
    match primitive,node.shape with
    | .Int integer signed,.int (.known actual) => signed && match integer,actual with
      | .I8,.i8 | .I16,.i16 | .I32,.i32 | .I64,.i64 | .I128,.i128 => true | _,_ => false
    | .Int integer signed,.uint (.known actual) => !signed && match integer,actual with
      | .I8,.u8 | .I16,.u16 | .I32,.u32 | .I64,.u64 | .I128,.u128 => true | _,_ => false
    | .Float actual,.float expected => match actual,expected with
      | .F16,.f16 | .F16B,.f16b | .F32,.f32 | .F64,.f64 | .X87F80,.x87f80 | .F128,.f128 | .PpcF128,.ppcf128 => true | _,_ => false
    | .Float actual,_ => match actual,node.sourceLayout.specialFloat with
      | .F16B,some .f16b | .X87F80,some .x87f80 | .PpcF128,some .ppcf128 => true
      | _,_ => false
    | .Pointer _,.rawPointer pointee .Mut =>
      match metadata.source.types[pointee]? with
      | some {shape := .tuple elements,..} => elements.isEmpty
      | _ => false
    | _,_ => false
  unless candidates.size == 1 do throw (.unsupported "canonical primitive type identity is absent or ambiguous")
  return (← require candidates[0]? "canonical primitive type").id

private def tagLayout (metadata : RuntimeMetadata) (tag : ABI.Scalar) : Result (TyAndLayout TypeId) := do
  let id ← primitiveType metadata tag.primitive
  let layout ← ConcreteLayout.scalarLayout metadata.target tag |>.mapError (fun message => .invalid "tag layout" message)
  pure ⟨id,layout⟩

def field (metadata : RuntimeMetadata) (parent : TyAndLayout TypeId) (index : Nat) :
    Result (TyAndLayout TypeId) := go (metadata.source.types.size+1) parent
where
  go : Nat → TyAndLayout TypeId → Result (TyAndLayout TypeId)
    | 0,_ => throw (.invalid "field layout" "cyclic unsafe binder")
    | fuel+1,parent => do
      let node ← metadata.node parent.ty
      if let .Multiple tag _ tagIndex _ := parent.layout.variants then
        if index == tagIndex then return ← tagLayout metadata tag
      let id ← match node.shape with
        | .tuple values => require values[index]? "tuple field"
        | .array element .. | .slice element => pure element
        | .str => return ← stringElementLayout metadata
        | .patternType base _ =>
          unless index == 0 do throw (.invalid "pattern field" "field index is not zero")
          pure base
        | .closure .. | .coroutineClosure .. => require node.sourceLayout.closureUpvars[index]? "closure capture"
        | .unsafeBinder inner _ => return ← go fuel {parent with ty := inner}
        | .adt data => do
          let .Single selected := parent.layout.variants | throw (.unsupported "ADT field requires a selected variant")
          let variant ← require data.variants[selected]? "ADT variant"
          let source ← require variant.fields[index]? "ADT field"
          pure source.typeId
        | .rawPointer pointee _ | .reference pointee .. => do
          unless index < parent.layout.fields.count do throw (.invalid "wide pointer field" "field index out of bounds")
          if index == 0 then
            let primitive : Primitive := .Pointer AddressSpace.ZERO
            let size ← primitive.size metadata.target |>.mapError (fun e => .invalid "pointer field" (reprStr e))
            let range ← WrappingRange.full size |>.mapError (fun e => .invalid "pointer field" (reprStr e))
            let range := if node.shapeKind == .reference then {range with start := 1} else range
            let layout ← ConcreteLayout.scalarLayout metadata.target (.Initialized (value := primitive) (validRange := range))
              |>.mapError (fun e => .invalid "pointer field" e)
            return ⟨parent.ty,layout⟩
          let tail ← ConcreteTypeLayout.pointerTail metadata.source (metadata.source.types.size+1) pointee
            |>.mapError (fun e => .invalid "pointer metadata" e)
          let candidates ← match tail with
            | .str | .slice _ => pure (metadata.source.types.filter fun source =>
                source.shapeMetadata.unsignedKind == some (.known .usize))
            | .dynamicTraitObject _ principal _ => do
              let definition ← principal.mapM fun id => do
                pure (← require metadata.source.predicates[id]? "dynamic principal").definitionId
              let count ← metadata.source.sourceTraits.vtableMinEntries definition
                |>.mapError (fun message => .invalid "vtable minimum entries" message)
              pure (metadata.source.types.filter fun source => match source.shape with
                | .reference array .Not .Static => match metadata.source.types[array]? with
                  | some {shape := .array element _ constructor,..} =>
                    constructor.count == count &&
                      (metadata.source.types[element]?).any (fun element => element.shapeMetadata.unsignedKind == some (.known .usize))
                  | _ => false
                | _ => false)
            | _ => throw (.invalid "pointer metadata" "wide pointer has a thin struct tail")
          unless candidates.size == 1 do throw (.unsupported "canonical pointer metadata type absent or ambiguous")
          pure (← require candidates[0]? "pointer metadata").id
        | .coroutine .. => do
          let material ← require node.sourceLayout.coroutine "coroutine source layout"
          match parent.layout.variants with
          | .Single selected =>
            let fields ← require material.variants[selected]? "coroutine variant"
            let saved ← require fields[index]? "coroutine variant field"
            require material.savedTypes[saved]? "coroutine saved field"
          | .Multiple .. => require material.prefix[index]? "coroutine prefix field"
          | .Empty => throw (.invalid "coroutine field" "empty coroutine layout")
        | _ => throw (.unsupported "type field query")
      metadata.lookup id

def forVariant (metadata : RuntimeMetadata) (parent : TyAndLayout TypeId) (index : Nat) :
    Result (TyAndLayout TypeId) := do
  let node ← metadata.node parent.ty
  match parent.layout.variants with
  | .Single actual =>
    if actual == index then return parent
    let canonical ← metadata.lookup parent.ty
    unless canonical.layout.variants == parent.layout.variants do
      throw (.invalid "variant projection" "cannot select another variant from a projected variant")
    let .adt data := node.shape | throw (.invalid "variant projection" "non-ADT single layout")
    let variant ← require data.variants[index]? "uninhabited ADT variant"
    return ⟨parent.ty,{ConcreteLayout.neverLayout metadata.target with
      variants := .Single index
      fields := if variant.fields.isEmpty then .Arbitrary #[] #[] else .Union variant.fields.size}⟩
  | .Empty =>
    let .adt data := node.shape | throw (.invalid "variant projection" "non-ADT empty layout")
    let variant ← require data.variants[index]? "uninhabited ADT variant"
    return ⟨parent.ty,{ConcreteLayout.neverLayout metadata.target with
      variants := .Single index
      fields := if variant.fields.isEmpty then .Arbitrary #[] #[] else .Union variant.fields.size}⟩
  | .Multiple _ _ _ variants =>
    let variant ← require variants[index]? "variant index"
    return ⟨parent.ty,{parent.layout with
      fields := .Arbitrary variant.fieldOffsets variant.fieldsInMemoryOrder
      variants := .Single index, backendRepr := variant.backendRepr
      largestNiche := variant.largestNiche, uninhabited := variant.uninhabited
      size := variant.size, randomizationSeed := 0}⟩

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
