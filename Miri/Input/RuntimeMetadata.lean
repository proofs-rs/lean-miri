import Miri.Input.Model
import Miri.Input.TypeArena
import Miri.Input.TypeArenaWorld
import Miri.Input.GenericInstantiationWorld
import Miri.Input.TermSized
import Miri.Input.TraitSelection.EnvironmentEntailment
import Miri.Input.WorldNormalization
import Miri.Input.WorldTypeMetadata
import Miri.Input.SourceDynamicView
import Miri.Input.SourceDynMethods
import Miri.Input.RelativeDiscriminants
import Miri.Input.SequenceLayoutMaterial
import Miri.ABI.SequenceLayout
import Miri.Input.StructuralNormalization
import Miri.Input.StructuralPointerMetadata
import Miri.ABI.Layout
import Miri.ABI.PrimitiveLayout
import Miri.ABI.UnivariantLayout
import Miri.ABI.StructLayout
import Miri.ABI.EnumLayout
import Miri.Input.StructLayoutMaterial
import Miri.ABI.UnionLayout
import Miri.ABI.PatternLayout
import Miri.Input.PatternLayoutMaterial
import Miri.Input.CoroutineSourceInstantiation
import Miri.Input.DefinitionPathHash
import Miri.ABI.CoroutineLayout

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
  if source.tupleType.isSome || source.unionType.isSome || source.structType.isSome || source.enumType.isSome ||
      source.patternType.isSome || source.sequenceType.isSome || source.pointerType.isSome || source.pointerDataType.isSome || source.enumTagType.isSome then
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


end RuntimeMetadata

private def rawLayoutBudget (types layouts : Nat) (definitions : Array DefinitionId) : Nat :=
  3 * (types + layouts + definitions.foldl (fun total definition => total + match definition.genericTemplate with
    | none => 1
    | some template => 1 + StructLayoutMaterial.termFuel template.typeExpression +
      template.fields.foldl (fun total field => total + StructLayoutMaterial.termFuel field.expression) 0) 1)

/-- Immutable compiler tables and target semantics. ID lookup directly indexes
validated dense tables; semantic layouts are constructed only on demand. -/
structure RuntimeMetadata where
  source : ImportDocument
  target : RuntimeTargetDataLayout
  /-- Raw syntax traversal budget, computed once; contains no query answer. -/
  materialLayoutFuel : Nat
  normalizationContext : AliasRuntime.Context
  /-- Immutable validation/index evidence tied to the exact raw source prefix. -/
  checkedMaterial : Option (TypeArena.CheckedMaterial source.types source.typeConstants
    source.definitions source.predicates target.pointerSize.bytes.toNat) := none
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
    let checked ← (TypeArena.CheckedMaterial.create document.types document.typeConstants
      document.definitions document.predicates target.pointerSize.bytes.toNat).mapError (fun e => .invalid "material prefix" e)
    let normalizationContext ← (AliasRuntime.Context.ofDocument document).mapError (fun e => .invalid "normalization material" e)
    return {
      source := document
      target := target
      normalizationContext := normalizationContext
      checkedMaterial := some checked
      materialLayoutFuel := rawLayoutBudget document.types.size document.layouts.size document.definitions,
      denseTypes := some ⟨dense⟩ }
  else throw (.invalid "compiler type ID" "material type IDs are not dense row positions")

def node (metadata : RuntimeMetadata) (id : TypeId) : Result TypeNode := do
  if metadata.denseTypes.isNone then
    (TypeArena.validateMaterial metadata.source.types).mapError (.invalid "type arena")
  let value ← require metadata.source.types[id]? "source type; constructed types require execution universe"
  unless value.id == id do throw (.invalid "type arena" "source type row/index mismatch")
  pure value

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

/-- The same source layout algorithm can run in the execution monad. A
normalization demand may allocate, execute CTFE and update typed memo state. -/
structure LayoutNormalization (m : Type → Type) extends AliasRuntime.Context where
  resolve : Nat → Nat → GenericSubstitution.Term → m TypeId

section EffectfulSourceLayouts
variable {m : Type → Type} [Monad m] [MonadStateOf TypeArena.World m]
  [MonadExceptOf String m] [MonadLiftT (Except String) m]
  [MonadLiftT TypeArena.WorldM m]

private def lift {m : Type → Type} [Monad m] [MonadExceptOf String m] (result : Except String α) : m α :=
  match result with | .ok value => pure value | .error error => throw error

private def worldIntegerName : MIR.IntegerKind → String
  | .i8 => "i8" | .i16 => "i16" | .i32 => "i32" | .i64 => "i64"
  | .i128 => "i128" | .isize => "isize" | .u8 => "u8" | .u16 => "u16"
  | .u32 => "u32" | .u64 => "u64" | .u128 => "u128" | .usize => "usize"

open TypeArena in
private def worldAdt (id : TypeId) : m (AdtDeclaration.Material × GenericSubstitution.DefinitionTemplate ×
    GenericSubstitution.DefinitionIdentity × Array MIR.GenericArg × Option AdtShape) := do
  let world ← get
  let (identity, args, shape) ← match ← lift (world.lookupType id) with
    | .material node => match node.shape with
      | .adt data => do
        let some definition := world.definitions[data.definition]? | throw "layout ADT definition absent"
        pure (⟨definition.crateIndex,definition.index⟩,data.args,some data)
      | _ => throw "layout source type is not an ADT"
    | .constructed (.adt identity args) => pure (identity,args,none)
    | _ => throw "layout constructed type is not an ADT"
  let reference ← lift (world.definitionRef identity)
  let some definition := world.definitions[reference]? | throw "layout ADT declaration absent"
  let some declaration := definition.adtDeclaration | throw "layout raw ADT declaration absent"
  let some template := definition.genericTemplate | throw "layout raw ADT field template absent"
  lift (declaration.validate template)
  unless args.size == template.parameters.size do throw "layout ADT generic argument arity mismatch"
  for (parameter,arg) in template.parameters.zip args do
    let sort : GenericSubstitution.ArgSort := match arg with
      | .Type _ => .type | .Lifetime _ => .region | .Const _ => .constant
    unless parameter == sort do throw "layout ADT generic argument sort mismatch"
  if let some shape := shape then
    unless shape.kind == declaration.kind && shape.representation == declaration.representation do
      throw "layout ADT material differs from raw declaration attributes"
    unless shape.variants.size == declaration.variantCount do
      throw "layout ADT variant domain differs from raw declaration"
    let materialFields := shape.variants.foldl (fun fields variant =>
      fields ++ variant.fields.map (fun field => (variant.index,field.index))) #[]
    unless materialFields == declaration.fields.map (fun field => (field.variantIndex,field.fieldIndex)) do
      throw "layout ADT field domain differs from raw declaration"
  pure (declaration,template,identity,args,shape)

open TypeArena in
private def worldAdtField (normalization : Option (LayoutNormalization m)) (fuel : Nat)
    (id variant index : Nat) : m TypeId := do
  let world ← get
  let (declaration,_,identity,args,_) ← worldAdt id
  unless variant < declaration.variantCount && declaration.fields.any (fun field =>
      field.variantIndex == variant && field.fieldIndex == index) do
    throw "constructed ADT field index absent"
  let term ← lift (GenericInstantiationWorld.instantiateFieldTerm world fuel identity args variant index)
  match normalization with
  | some context => context.resolve (fuel * (fuel + 1)) fuel term
  | none => GenericInstantiationWorld.resolveType fuel term

open TypeArena in
private def worldAdtFields (normalization : Option (LayoutNormalization m)) (fuel : Nat)
    (id variant : Nat) : m (Array TypeId) := do
  let (declaration,_,_,_,_) ← worldAdt id
  unless variant < declaration.variantCount do throw "layout ADT variant index absent"
  let fields := declaration.fields.filter (·.variantIndex == variant)
  fields.mapM fun field => worldAdtField normalization fuel id variant field.fieldIndex

open TypeArena in
private def worldAdtLastField (normalization : Option (LayoutNormalization m)) (fuel : Nat)
    (id : Nat) : m (Option TypeId) := do
  let (declaration,_,_,_,_) ← worldAdt id
  let fields := declaration.fields.filter (·.variantIndex == 0)
  let some last := fields.back? | return none
  return some (← worldAdtField normalization fuel id 0 last.fieldIndex)

private def worldRepresentation (source : ReprOptions) : Except String UnivariantLayout.Representation := do
  unless source.flagsBits < 256 do throw "layout representation flags overflow u8"
  pure {
    flags := UInt8.ofNat source.flagsBits, integerRepresentation := source.integer.isSome
    align := ← source.alignBytes.mapM (fun value => (alignment value).mapError toString)
    pack := ← source.packBytes.mapM (fun value => (alignment value).mapError toString)
    fieldShuffleSeed := ← (u64 source.fieldShuffleSeed "layout field shuffle seed").mapError toString }

private def worldEnumInteger : ReprInteger → Except String IntegerType
  | .pointerSized signed => pure (.Pointer signed)
  | .fixed (.known kind) bits signed => do
    let integer ← match kind with
      | .i8 | .u8 => pure Integer.I8 | .i16 | .u16 => pure .I16
      | .i32 | .u32 => pure .I32 | .i64 | .u64 => pure .I64
      | .i128 | .u128 => pure .I128
      | .isize | .usize => throw "fixed enum repr uses a pointer-sized integer kind"
    -- rustc_abi::Integer names the width with `int_ty_str` even when
    -- IntegerType carries unsigned signedness separately.
    unless integer.size.bytes.toNat * 8 == bits do
      throw "enum representation integer kind/size disagree"
    pure (.Fixed integer signed)

open TypeArena in
private def worldConstructor (id : TypeId) : m Constructor := do
  let world ← get
  match ← lift (world.lookupType id) with
  | .constructed key => pure key
  | .material node =>
    let some key ← lift (world.materialKey node) | throw "layout source constructor has no universe key"
    pure key

open TypeArena in
/-- layout.rs975-987 and rustc_type_ir/ty_kind/closure.rs138-173,250-281:
closure fields are the actual capture tuple's fields. The raw generic header
checks the parent prefix and synthetic suffix before selecting upvars. -/
private def worldClosureFields (id : TypeId) : m (Array TypeId) := do
  let (owner,arguments,suffix) ← match ← worldConstructor id with
    | .closure owner arguments => pure (owner,arguments,3)
    | .coroutineClosure owner arguments => pure (owner,arguments,4)
    | _ => throw "capture fields require a closure constructor"
  let world ← get
  let reference ← lift (world.definitionRef owner)
  let some definition := world.definitions[reference]? | throw "capture field owner absent"
  let some path := definition.rawPath | throw "capture field raw generic header absent"
  unless path.components.back?.any (·.kind == "closure") do
    throw "capture field raw owner is not a closure"
  let header ← lift (DefinitionPath.requireGenerics path)
  unless header.parameters.size == arguments.size &&
      header.parentParameterCount + suffix == arguments.size do
    throw "capture field canonical synthetic scope mismatch"
  for (sort,argument) in header.parameters.zip arguments do
    let actual : GenericSubstitution.ArgSort := match argument with
      | .Type _ => .type | .Const _ => .constant | .Lifetime _ => .region
    unless sort == actual do throw "capture field generic argument sort mismatch"
  let some (MIR.GenericArg.Type captures) := arguments[header.parentParameterCount + 2]?
    | throw "capture field tuple argument absent"
  let .tuple fields ← worldConstructor captures | throw "capture field upvars are not a tuple"
  pure fields

open TypeArena in
private def worldSized (normalization : Option (LayoutNormalization m)) : Nat → TypeId → m Bool
  | 0, _ => throw "layout source sizedness recursion exhausted"
  | fuel + 1, id => do
    let world ← get
    match ← lift (world.lookupType id) with
    | .material node => match node.shape with
      | .str | .slice .. | .dynamicTraitObject .. | .foreign .. => pure false
      | .tuple elements => match elements.back? with
        | none => pure true | some tail => worldSized normalization fuel tail
      | .adt data =>
        if data.kind != .structKind then return true
        let (_,template,_,_,_) ← worldAdt id
        if template.fields.back?.any (fun field => StructLayoutMaterial.guaranteedSized
            (StructLayoutMaterial.termFuel field.expression + 1) field.expression) then return true
        match ← worldAdtLastField normalization fuel id with
        | none => pure true | some tail => worldSized normalization fuel tail
      | .alias .. => throw "layout sizedness requires source alias normalization"
      | _ => pure true
    | .constructed key => match key with
      | .str | .slice .. | .foreign .. | .dynamic .. => pure false
      | .tuple elements => match elements.back? with
        | none => pure true | some tail => worldSized normalization fuel tail
      | .adt .. =>
        let (declaration,template,_,_,_) ← worldAdt id
        if declaration.kind != .structKind then return true
        if template.fields.back?.any (fun field => StructLayoutMaterial.guaranteedSized
            (StructLayoutMaterial.termFuel field.expression + 1) field.expression) then return true
        match ← worldAdtLastField normalization fuel id with
        | none => pure true | some tail => worldSized normalization fuel tail
      | .alias .. => throw "layout sizedness requires source alias normalization"
      | _ => pure true

open TypeArena in
private def worldStructSized (normalization : Option (LayoutNormalization m)) (fuel : Nat)
    (declaration : AdtDeclaration.Material) (template : GenericSubstitution.DefinitionTemplate) : m Bool := do
  let some tail := template.fields.back? | return true
  if StructLayoutMaterial.guaranteedSized (StructLayoutMaterial.termFuel tail.expression + 1) tail.expression then
    return true
  if let some context := normalization then
    let sized := context.traits.traits.filter (·.langItem == some "sized")
    unless sized.size <= 1 do throw "layout declaration environment has ambiguous canonical Sized trait"
    if let some sized := sized[0]? then
      let goal : TraitSelection.Clause := ⟨#[],.trait ⟨.positive,⟨sized.definition,#[tail.expression]⟩⟩⟩
      let .definition .type "adt" identity _ := template.typeExpression
        | throw "layout declaration environment lacks a nominal source identity"
      let assumptions ← lift (SourceEnvironment.predicates
        (SourceEnvironmentRuntime.lookupDefinitions context.generic.definitions) (fuel + 1) identity)
      let proof ← lift (TraitSelection.EnvironmentEntailment.entails context.traits
        template.parameters assumptions (fuel * (fuel + 1)) goal)
      if proof.isSome then return true
  -- Pinned core ManuallyDrop<T: ?Sized> retains the raw T constraint.
  -- Its instantiated T can be sized while the declaration stays MaybeUnsized.
  -- Recognize only this complete raw header/scope, never catalogue absence.
  if declaration.langItem == some "manually_drop" then
    unless template.parameters == #[.type] && template.fields.size == 1 do
      throw "ManuallyDrop declaration Sized source header is malformed"
    let some field := template.fields[0]? | throw "ManuallyDrop raw field absent"
    unless field.variantIndex == 0 && field.fieldIndex == 0 &&
        field.expression == .parameter .type 0 do
      throw "ManuallyDrop declaration Sized source tail is malformed"
    let .definition .type "adt" identity (.cons (.parameter .type 0) .nil) := template.typeExpression
      | throw "ManuallyDrop declaration Sized physical header is malformed"
    let world ← get
    let reference ← lift (world.definitionRef identity)
    let some owner := world.definitions[reference]? | throw "ManuallyDrop physical owner absent"
    unless owner.adtDeclaration == some declaration && owner.genericTemplate == some template do
      throw "ManuallyDrop declaration Sized physical owner mismatch"
    let scope ← lift (SourceEnvironmentRuntime.lookupDefinitions world.definitions identity)
    unless scope.parameters == #[.type] && scope.parent.isNone && scope.genericParent.isNone && !scope.isTrait do
      throw "ManuallyDrop declaration Sized source scope is malformed"
    let some context := normalization | throw "ManuallyDrop declaration Sized requires canonical MetaSized source"
    let metaSources := context.traits.traits.filter (·.langItem == some "meta_sized")
    unless metaSources.size == 1 do throw "ManuallyDrop canonical MetaSized source absent or ambiguous"
    let some metaSource := metaSources[0]? | throw "ManuallyDrop canonical MetaSized source absent"
    unless metaSource.parameters == #[.type] && !metaSource.isAlias && metaSource.superPredicates.isEmpty do
      throw "ManuallyDrop canonical MetaSized source header is malformed"
    let expected : TraitSelection.Clause := ⟨#[],.trait ⟨.positive,⟨metaSource.definition,#[.parameter .type 0]⟩⟩⟩
    unless scope.ownPredicates == #[expected] do
      throw "ManuallyDrop declaration Sized source is outside the pinned MetaSized-only scope"
    return false
  -- A missing positive environment proof remains unknown. Only the separate
  -- structural source algorithm below may establish its supported cases;
  -- generic parameter tails remain explicit unsupported obligations.
  let world ← get
  lift (TermSized.query {
    sourceAdt := fun identity => do
      let reference ← world.definitionRef identity
      let some definition := world.definitions[reference]? | throw "layout sizedness ADT definition absent"
      let some declaration := definition.adtDeclaration | throw "layout sizedness raw ADT declaration absent"
      let some template := definition.genericTemplate | throw "layout sizedness raw field template absent"
      declaration.validate template
      pure (declaration.kind,template),
    normalizeAlias := fun remaining term => match normalization with
      | none => throw "layout declaration sizedness requires ParamEnv alias normalization"
      | some context => AliasRuntime.normalizeTerm context.toContext (remaining * (remaining + 1)) remaining #[] #[] term }
    .sized fuel tail.expression)

private def worldArrayCount (target : RuntimeTargetDataLayout) (length : TypeConstantId)
      (identity : ArrayConstructor) : m UInt64 := do
    let world ← get
    lift (SequenceLayoutMaterial.arrayCount
      (fun id => do
        match ← world.lookupType id with
        | .material node => pure (node.shapeMetadata.unsignedKind == some (.known .usize))
        | .constructed (.integer false .usize) => pure true
        | _ => pure false)
      world.lookupConstant target.pointerSize.bytes.toNat length identity)

/-- Ephemeral answers for canonical layout-of-type demands only. Contextual
layout seeds (pointer data, tags, variants) never share this key space. The
entire map is discarded at the end of this one query, outside the type World. -/
private abbrev LayoutQuery (m : Type → Type) := StateT (Std.HashMap TypeId LayoutData) m

private def liftWorld (action : m α) : LayoutQuery m α := fun cache => do
  pure ((← action),cache)

mutual
  private def worldMetadata (normalization : Option (LayoutNormalization m)) (target : RuntimeTargetDataLayout) (layouts : Array Input.Layout) (coroutineSources : Array CoroutineGenericSource) : Nat → TypeId → LayoutQuery m (Option LayoutData)
    | 0, _ => throw "layout pointer metadata recursion exhausted"
    | fuel + 1, id => do
      if ← liftWorld (worldSized normalization (fuel + 1) id) then return none
      let world ← liftWorld get
      match ← lift (world.lookupType id) with
      | .material node => match node.shape with
        | .str | .slice .. => return some (← lift (PrimitiveLayout.compute target "usize"))
        | .foreign .. => pure none
        | .tuple elements =>
          let some tail := elements.back? | throw "unsized tuple has no tail"
          worldMetadata normalization target layouts coroutineSources fuel tail
        | .adt .. =>
          let some tail ← liftWorld (worldAdtLastField normalization fuel id) | throw "unsized struct has no tail"
          worldMetadata normalization target layouts coroutineSources fuel tail
        | .dynamicTraitObject .. => do
          let metadata ← liftWorld (WorldTypeMetadata.dynMetadataType id)
          return some (← worldRawMetadataLayout normalization target fuel metadata)
        | _ => throw "layout source pointer metadata constructor unsupported"
      | .constructed key => match key with
        | .dynamic .. => do
          let metadata ← liftWorld (WorldTypeMetadata.dynMetadataType id)
          return some (← worldRawMetadataLayout normalization target fuel metadata)
        | .str | .slice .. => return some (← lift (PrimitiveLayout.compute target "usize"))
        | .foreign .. => pure none
        | .tuple elements =>
          let some tail := elements.back? | throw "unsized tuple has no tail"
          worldMetadata normalization target layouts coroutineSources fuel tail
        | .adt .. =>
          let some tail ← liftWorld (worldAdtLastField normalization fuel id) | throw "unsized struct has no tail"
          worldMetadata normalization target layouts coroutineSources fuel tail
        | _ => throw "layout constructed pointer metadata constructor unsupported"

  /-- Source-only DynMetadata representation. Even a reused material identity
  traverses raw field templates; no physical layout row is consulted. Pinned
  core::ptr::{DynMetadata,NonNull} uses a NotNull raw pointer and PhantomData. -/
  private def worldRawMetadataLayout (normalization : Option (LayoutNormalization m))
      (target : RuntimeTargetDataLayout) : Nat → TypeId → LayoutQuery m LayoutData
    | 0, _ => throw "raw metadata layout recursion exhausted"
    | fuel + 1, id => do
      let key ← liftWorld (worldConstructor id)
      match key with
      | .adt .. =>
        let (declaration,template,identity,args,_) ← liftWorld (worldAdt id)
        unless declaration.kind == .structKind &&
            #[some "dyn_metadata",some "non_null",some "phantom_data"].contains declaration.langItem do
          throw "raw metadata field ADT source is outside the checked representation"
        let some context := normalization | throw "raw metadata fields need source normalization"
        let types ← declaration.fields.mapM fun field => liftWorld do
          let term ← lift (GenericInstantiationWorld.instantiateFieldTerm (← get) fuel identity args
            field.variantIndex field.fieldIndex)
          context.resolve (fuel * (fuel + 1)) fuel term
        let fields ← types.mapM (worldRawMetadataLayout normalization target fuel)
        let repr ← lift (worldRepresentation declaration.representation)
        let alwaysSized ← liftWorld (worldStructSized normalization fuel declaration template)
        lift (StructLayout.compute target fields repr 0 false alwaysSized .enabled)
      | .patternType base pattern =>
        let baseLayout ← worldRawMetadataLayout normalization target fuel base
        let world ← liftWorld get
        lift (PatternLayoutMaterial.compute world.lookupConstant target base baseLayout pattern)
      | .rawPointer pointee _ =>
        let world ← liftWorld get
        unless (← lift (world.shapeKind pointee)) == .foreign do
          throw "raw metadata vtable pointer requires its foreign source pointee"
        lift (PrimitiveLayout.pointer target false none)
      | _ => throw "raw metadata field constructor is outside the checked representation"

  private def worldLayoutType (normalization : Option (LayoutNormalization m)) (target : RuntimeTargetDataLayout) (layouts : Array Input.Layout) (coroutineSources : Array CoroutineGenericSource) :
      Nat → TypeId → LayoutQuery m LayoutData
    | 0, _ => throw "universe layout recursion exhausted"
    | fuel + 1, id => do
      let cache ← get
      if let some cached := cache[id]? then return cached
      let world ← liftWorld get
      let result ← match ← lift (world.lookupType id) with
        | .material node => match node.shape with
          | .coroutine .. => do
            let key ← liftWorld (worldConstructor id)
            worldLayoutConstructor normalization target layouts coroutineSources fuel id key
          | .adt data =>
            if (world.definitions[data.definition]?).any (fun source =>
                source.adtDeclaration.any (·.langItem == some "dyn_metadata")) then
              worldRawMetadataLayout normalization target fuel id
            else worldLayoutSeed normalization target layouts coroutineSources fuel node.layoutId
          | _ => worldLayoutSeed normalization target layouts coroutineSources fuel node.layoutId
        | .constructed key => worldLayoutConstructor normalization target layouts coroutineSources fuel id key
      modify fun cache => cache.insert id result
      pure result

  termination_by structural fuel _ => fuel

  private def worldLayoutConstructor (normalization : Option (LayoutNormalization m)) (target : RuntimeTargetDataLayout) (layouts : Array Input.Layout) (coroutineSources : Array CoroutineGenericSource) :
      Nat → TypeId → TypeArena.Constructor → LayoutQuery m LayoutData
    | 0, _, _ => throw "universe constructor layout recursion exhausted"
    | fuel + 1, id, key => match key with
      | .bool => lift (PrimitiveLayout.compute target "bool")
      | .char => lift (PrimitiveLayout.compute target "char")
      | .never => lift (PrimitiveLayout.compute target "never")
      | .functionPointer _ => lift (PrimitiveLayout.compute target "fn_pointer")
      | .integer signed kind => do
        unless signed == kind.signed do throw "universe integer signedness disagrees with constructor"
        lift (PrimitiveLayout.compute target (worldIntegerName kind))
      | .float kind => do
        let value : Primitive := .Float (match kind with
          | .f16 => .F16 | .f16b => .F16B | .f32 => .F32 | .f64 => .F64
          | .f128 => .F128 | .ppcf128 => .PpcF128)
        let size ← lift (value.size target |>.mapError toString)
        let range ← lift (WrappingRange.full size |>.mapError reprStr)
        lift (PrimitiveLayout.scalar target value range)
      | .str => lift (SequenceLayout.str target)
      | .slice element => do
        let element ← worldLayoutType normalization target layouts coroutineSources fuel element
        lift (SequenceLayout.slice target element)
      | .array element length => do
        let world ← liftWorld get
        let constant ← lift (world.lookupConstant length)
        let .Value _ tree := constant | throw "universe array length requires constant evaluation"
        let some (Miri.MIR.ValTreeNode.Leaf bits _) := tree.nodes[tree.root]?
          | throw "universe array length is not a scalar"
        let identity ← match ← lift (world.lookupType id) with
          | .material node => match node.shape with
            | .array _ _ identity => pure identity
            | _ => throw "array layout constructor source mismatch"
          | .constructed _ => pure ⟨bits,true⟩
        let count ← liftWorld (worldArrayCount target length identity)
        let element ← worldLayoutType normalization target layouts coroutineSources fuel element
        unless element.isSized do throw "universe array element is unsized"
        lift (SequenceLayout.arrayLike target element (some count))
      | .tuple elements => do
        let fields ← elements.mapM (worldLayoutType normalization target layouts coroutineSources fuel)
        lift (UnivariantLayout.compute target fields {} (if fields.isEmpty then .alwaysSized else .maybeUnsized))
      | .rawPointer pointee _ => do
        let metadata ← worldMetadata normalization target layouts coroutineSources fuel pointee
        lift (PrimitiveLayout.pointer target false metadata)
      | .reference pointee .. => do
        let metadata ← worldMetadata normalization target layouts coroutineSources fuel pointee
        lift (PrimitiveLayout.pointer target true metadata)
      | .patternType base pattern => do
        let baseLayout ← worldLayoutType normalization target layouts coroutineSources fuel base
        let world ← liftWorld get
        lift (PatternLayoutMaterial.compute world.lookupConstant target base baseLayout pattern)
      | .coroutine owner _ => do
        let world ← liftWorld get
        let term ← lift (GenericInstantiationWorld.ofType world fuel id)
        let instantiated ← lift (CoroutineSourceInstantiation.instantiate coroutineSources fuel term)
        let wrappers := world.definitions.filter fun definition =>
          definition.adtDeclaration.any (·.langItem == some "maybe_uninit")
        unless wrappers.size == 1 do throw "coroutine MaybeUninit declaration missing or ambiguous"
        let some wrapper := wrappers[0]? | throw "coroutine MaybeUninit declaration absent"
        let wrapperIdentity : GenericSubstitution.DefinitionIdentity := ⟨wrapper.crateIndex,wrapper.index⟩
        let resolve (term : GenericSubstitution.Term) := match normalization with
          | none => GenericInstantiationWorld.resolveType fuel term
          | some context => context.resolve (fuel * (fuel + 1)) fuel term
        let saved ← instantiated.saved.mapM fun term => do
          let value ← liftWorld (resolve term)
          let wrapped ← liftWorld (TypeArena.World.internType (.adt wrapperIdentity #[.Type value]))
          worldLayoutType normalization target layouts coroutineSources fuel wrapped
        let upvars ← instantiated.upvars.mapM fun term => do
          let value ← liftWorld (resolve term)
          worldLayoutType normalization target layouts coroutineSources fuel value
        let layout ← lift (CoroutineLayout.compute target saved upvars
          instantiated.source.layout.variants instantiated.source.layout.storageConflicts)
        let world ← liftWorld get
        let reference ← lift (world.definitionRef owner)
        let some definition := world.definitions[reference]? | throw "coroutine logical definition absent"
        let some path := definition.rawPath | throw "coroutine logical definition path absent"
        let fingerprint ← lift (DefinitionPathHash.query path)
        let low := UInt64.ofNat fingerprint.toNat
        let high := UInt64.ofNat (fingerprint.toNat / 2^64)
        -- Pinned Fingerprint::to_smaller_hash: low*3 + high, wrapping.
        pure {layout with randomizationSeed := low * 3 + high}
      | .adt .. => do
        let (declaration,_,_,_,_) ← liftWorld (worldAdt id)
        if declaration.langItem == some "dyn_metadata" then
          worldRawMetadataLayout normalization target fuel id
        else worldAdtLayout normalization target layouts coroutineSources fuel id
      | .functionDefinition .. | .foreign .. =>
        pure {
          fields := .Arbitrary #[] #[]
          variants := .Single 0
          backendRepr := .Memory (sized := match key with | .functionDefinition .. => true | _ => false),
          largestNiche := none, uninhabited := false, align := .new target.i8Align,
          size := Size.ZERO, maxReprAlign := none, unadjustedAbiAlign := target.i8Align,
          reprC := false, randomizationSeed := 0 }
      | _ => throw "universe layout constructor is not implemented"
  termination_by structural fuel _ _ => fuel

  private def worldAdtLayout (normalization : Option (LayoutNormalization m)) (target : RuntimeTargetDataLayout) (layouts : Array Input.Layout) (coroutineSources : Array CoroutineGenericSource)
      : Nat → TypeId → LayoutQuery m LayoutData
    | 0, _ => throw "universe ADT layout recursion exhausted"
    | fuel + 1, id => do
      let (declaration,template,_,_,_) ← liftWorld (worldAdt id)
      let repr ← lift (worldRepresentation declaration.representation)
      unless declaration.representation.flagsBits &&& (2 + 64) == 0 do
        throw "universe SIMD/scalable ADT layout is not implemented"
      unless declaration.langItem != some "f16b" && declaration.langItem != some "ppcf128" do
        throw "universe special float ADT layout is not implemented"
      let niches := if declaration.langItem == some "unsafe_cell" || declaration.langItem == some "unsafe_pinned"
        then StructLayout.NicheOptimizations.disabled else .enabled
      if declaration.kind == .enumKind then
        let variants ← (List.range declaration.variantCount).toArray.mapM fun index => do
          let types ← match normalization with
            | none => liftWorld (worldAdtFields none fuel id index)
            | some context => liftWorld do
              let (_,_,identity,args,_) ← worldAdt id
              let sourceFields := declaration.fields.filter (·.variantIndex == index)
              sourceFields.mapM fun field => do
                let term ← lift (GenericInstantiationWorld.instantiateFieldTerm (← get) fuel identity args index field.fieldIndex)
                context.resolve (fuel * (fuel + 1)) fuel term
          types.mapM (worldLayoutType normalization target layouts coroutineSources fuel)
        let integerRepr ← lift (declaration.representation.integer.mapM worldEnumInteger)
        -- Explicit expressions remain a CTFE obligation; optimized empty/single
        -- branches do not inspect their values.
        let discriminants ← lift (RelativeDiscriminants.values (target.pointerSize.bytes.toNat * 8) declaration)
        return ← lift (EnumLayout.compute target variants repr integerRepr (discriminants.getD #[]) niches)
      let types ← liftWorld (worldAdtFields normalization fuel id 0)
      let fields ← types.mapM (worldLayoutType normalization target layouts coroutineSources fuel)
      if declaration.kind == .unionKind then return ← lift (UnionLayout.compute target fields repr)
      unless declaration.kind == .structKind do throw "universe enum layout is not implemented"
      let alwaysSized ← liftWorld (worldStructSized normalization fuel declaration template)
      lift (StructLayout.compute target fields repr 0 false alwaysSized niches)
  termination_by structural fuel _ => fuel

  private def worldLayoutSeed (normalization : Option (LayoutNormalization m)) (target : RuntimeTargetDataLayout) (layouts : Array Input.Layout) (coroutineSources : Array CoroutineGenericSource) :
      Nat → LayoutId → LayoutQuery m LayoutData
    | 0, _ => throw "universe layout recipe recursion exhausted"
    | fuel + 1, id => do
      let some source := layouts[id]? | throw "universe layout seed absent"
      let constructors := #[source.structType.isSome,source.enumType.isSome,source.unionType.isSome,source.tupleType.isSome,
        source.primitiveRecipe.isSome,source.patternType.isSome,source.sequenceType.isSome,source.pointerType.isSome,source.pointerDataType.isSome,source.enumTagType.isSome].filter (fun enabled => enabled)
      unless constructors.size <= 1 do throw "conflicting universe layout recipe constructors"
      if let some ty := source.structType then
        let (declaration,_,_,_,_) ← liftWorld (worldAdt ty)
        unless declaration.kind == .structKind do throw "struct recipe source is not a struct"
        return ← worldAdtLayout normalization target layouts coroutineSources fuel ty
      if let some ty := source.enumType then
        let (declaration,_,_,_,_) ← liftWorld (worldAdt ty)
        unless declaration.kind == .enumKind do throw "enum recipe source is not an enum"
        return ← worldAdtLayout normalization target layouts coroutineSources fuel ty
      if let some ty := source.unionType then
        let (declaration,_,_,_,_) ← liftWorld (worldAdt ty)
        unless declaration.kind == .unionKind do throw "union recipe source is not a union"
        return ← worldAdtLayout normalization target layouts coroutineSources fuel ty
      if let some ty := source.tupleType then
        let key ← liftWorld (worldConstructor ty)
        let .tuple elements := key | throw "tuple layout recipe source is not a tuple"
        return ← worldLayoutConstructor normalization target layouts coroutineSources fuel ty (.tuple elements)
      if let some ty := source.patternType then
        let world ← liftWorld get
        let .material node ← lift (world.lookupType ty)
          | throw "pattern recipe requires raw source pattern material"
        let .patternType base pattern := node.shape
          | throw "pattern recipe source is not a pattern"
        let baseLayout ← worldLayoutType normalization target layouts coroutineSources fuel base
        return ← lift (PatternLayoutMaterial.compute world.lookupConstant target base baseLayout pattern)
      if let some ty := source.sequenceType then
        let key ← liftWorld (worldConstructor ty)
        unless (match key with | .array .. | .slice .. | .str => true | _ => false) do
          throw "sequence recipe source is not a sequence"
        return ← worldLayoutConstructor normalization target layouts coroutineSources fuel ty key
      if let some ty := source.enumTagType then
        let parent ← worldLayoutType normalization target layouts coroutineSources fuel ty
        let .Multiple tag _ _ _ := parent.variants | throw "tag operation parent has no discriminant field"
        let .Initialized (value := value) (validRange := range) := tag
          | throw "tag operation requires initialized discriminant scalar"
        return ← lift (PrimitiveLayout.scalar target value range)
      if let some ty := source.pointerDataType then
        let key ← liftWorld (worldConstructor ty)
        let isReference ← match key with
          | .rawPointer .. => pure false | .reference .. => pure true
          | _ => throw "pointer data recipe source is not a pointer"
        let canonical ← worldLayoutType normalization target layouts coroutineSources fuel ty
        unless canonical.fields.count > 0 do throw "thin pointer has no data projection field"
        return ← lift (PrimitiveLayout.pointer target isReference none)
      if let some ty := source.pointerType then
        let key ← liftWorld (worldConstructor ty)
        unless (match key with | .rawPointer .. | .reference .. => true | _ => false) do
          throw "pointer recipe source is not a pointer"
        return ← worldLayoutConstructor normalization target layouts coroutineSources fuel ty key
      lift ((layout target source).mapError toString)


  termination_by structural fuel _ => fuel

end

/-- A canonical layout demand consumes the exact rustc LayoutData exported for
this material type. The execution World verifies its identity; locally interned
types cannot borrow a numeric row from the immutable compiler prefix. -/
def layoutEffectfulInWorld (normalization : LayoutNormalization m) (metadata : RuntimeMetadata) (id : TypeId) : m (TyAndLayout TypeId) := do
  let _ := normalization
  let actual ← match ← lift ((← get).lookupType id) with
    | .material node => pure node
    | .constructed constructor =>
      throw s!"constructed type {id} ({reprStr constructor}) has no rustc canonical layout result"
  let some original := metadata.source.types[id]?
    | throw "canonical layout type is absent from rustc export"
  unless actual.id == id && actual.layoutId == original.layoutId &&
      (← lift ((← get).materialKey actual)) == (← lift ((← get).materialKey original)) do
    throw "canonical layout type differs from rustc export"
  let some seed := metadata.source.layouts[original.layoutId]?
    | throw "rustc canonical layout result is absent"
  let result ← lift ((layout metadata.target seed).mapError toString)
  pure ⟨id,result⟩

end EffectfulSourceLayouts

private def pureLayoutNormalization (context : AliasRuntime.Context) : LayoutNormalization TypeArena.WorldM :=
  {toContext := context,resolve := WorldNormalization.resolveNormalizedTerm context}

/-- Pure source-only consumers retain the same execution-owned World. They do
not gain a CTFE capability; constant aliases still fail at their real demand. -/
def layoutInWorld (metadata : RuntimeMetadata) (id : TypeId) : TypeArena.WorldM (TyAndLayout TypeId) :=
  layoutEffectfulInWorld (pureLayoutNormalization metadata.normalizationContext) metadata id

private structure ScalarStorage where
  size : Size
  align : Align
  kind : Nat

mutual
/-- Storage geometry only: the second component records Memory/Scalar/ScalarPair.
Pinned rustc_ty_utils/layout.rs:241–310 clones a Pattern's base LayoutData and
changes validity/niches, never size. rustc_abi/layout.rs::univariant_biased
preserves the single field's geometry for the narrow repr(transparent) case.
No Pattern endpoint is evaluated here; this is not a value-validity judgment. -/
private def worldScalarStorage (target : RuntimeTargetDataLayout) (layouts : Array Input.Layout)
    (seen : Array TypeId) :
    Nat → TypeId → TypeArena.WorldM ScalarStorage
  | 0, _ => throw "scalar storage geometry recursion exhausted"
  | fuel + 1, id => do
    if seen.contains id then throw "cyclic scalar storage source type"
    let seen := seen.push id
    match ← worldConstructor id with
    | .patternType base pattern =>
      let storage ← worldScalarStorage target layouts seen fuel base
      let kind := storage.kind
      match pattern with
      | .range .. => unless kind == 1 do throw "range Pattern storage base is not scalar"
      | .notNull => unless kind == 1 || kind == 2 do throw "nonnull Pattern storage base is not scalar or scalar-pair"
      | .or _ => throw "or Pattern scalar storage is not implemented"
      pure storage
    | .adt .. =>
      let (declaration,_,_,_,_) ← worldAdt id
      -- No inference from material field IDs or cached normalized projections.
      -- Additional fields, repr modifiers and enum niches need full layout.
      if declaration.kind == .structKind && declaration.variantCount == 1 &&
          declaration.fields.size == 1 && declaration.representation.flagsBits == 4 &&
          declaration.representation.integer.isNone && declaration.representation.alignBytes.isNone &&
          declaration.representation.packBytes.isNone && declaration.representation.scalableElement.isNone then
        let (_,_,identity,args,_) ← worldAdt id
        let term ← lift (GenericInstantiationWorld.instantiateFieldTerm (← get) fuel identity args 0 0)
        let field ← worldScalarStorageTerm target layouts seen fuel term
        let align := target.aggregateAlign.max field.align
        let size ← lift ((field.size.alignTo align).mapError toString)
        let kind := if align == field.align && size == field.size then field.kind else 0
        pure ⟨size,align,kind⟩
      else
        let layout ← (worldLayoutType none target layouts #[] fuel id).run' {}
        pure ⟨layout.size,layout.align.abi, match layout.backendRepr with | .Scalar .. => 1 | .ScalarPair .. => 2 | _ => 0⟩
    | _ =>
      let layout ← (worldLayoutType none target layouts #[] fuel id).run' {}
      pure ⟨layout.size,layout.align.abi, match layout.backendRepr with | .Scalar .. => 1 | .ScalarPair .. => 2 | _ => 0⟩

private def worldScalarStorageTerm (target : RuntimeTargetDataLayout) (layouts : Array Input.Layout)
    (seen : Array TypeId) :
    Nat → GenericSubstitution.Term → TypeArena.WorldM ScalarStorage
  | 0, _ => throw "scalar storage raw field recursion exhausted"
  | fuel + 1, term => do
    match term with
    | .node .type "pattern" "" (.cons base (.cons pattern .nil)) =>
      let kind ← match pattern with
        | .node .aggregate "pattern_range" "" (.cons start (.cons finish .nil)) =>
          unless start.sort == .constant && finish.sort == .constant do
            throw "scalar storage range endpoint sort mismatch"
          pure 1
        | .atom .aggregate "pattern_not_null" "" => pure 2
        | _ => throw "scalar storage raw Pattern syntax is not implemented"
      let storage ← worldScalarStorageTerm target layouts seen fuel base
      let baseKind := storage.kind
      unless baseKind == 1 || (kind == 2 && baseKind == 2) do
        throw "scalar storage raw Pattern base ABI mismatch"
      pure storage
    | _ =>
      let id ← GenericInstantiationWorld.resolveType fuel term
      worldScalarStorage target layouts seen fuel id
end

/-- Physical source-only adapter. LayoutData contains no newly allocated type
IDs; execution providers must use layoutInWorld and retain its updated World. -/
def resolveLayout (target : RuntimeTargetDataLayout) (_types : Array TypeNode)
    (layouts : Array Input.Layout) (id : LayoutId) (_definitions : Array DefinitionId)
    (_constants : Array MIR.TypeConst) (_predicates : Array VtablePredicate) : Result LayoutData := do
  let source ← require layouts[id]? "compiler layout ID out of bounds"
  layout target source

/-- Decode rustc's exact material layout for scalar-wire width validation.
The closure owns only immutable source arrays; it keeps no query memo. -/
def scalarStorageQuery (target : RuntimeTargetDataLayout) (types : Array TypeNode)
    (layouts : Array Input.Layout) (_definitions : Array DefinitionId)
    (_constants : Array MIR.TypeConst) (_predicates : Array VtablePredicate) : Result (TypeId → Result Nat) := do
  pure fun id => do
    let node ← require types[id]? "scalar storage type ID out of bounds"
    let source ← require layouts[node.layoutId]? "scalar storage rustc layout result absent"
    let value ← layout target source
    pure value.size.bytes.toNat

/-- ID-free standalone adapter. Decoder captures scalarStorageQuery once for
all scalar-wire checks, rather than rebuilding the checked prefix per value. -/
def scalarStorageSize (target : RuntimeTargetDataLayout) (types : Array TypeNode)
    (layouts : Array Input.Layout) (definitions : Array DefinitionId)
    (constants : Array MIR.TypeConst) (predicates : Array VtablePredicate) (id : TypeId) : Result Nat := do
  (← scalarStorageQuery target types layouts definitions constants predicates) id

def lookup (metadata : RuntimeMetadata) (id : TypeId) : Result (TyAndLayout TypeId) := do
  unless id < metadata.source.types.size do
    throw (.unsupported "constructed type layout requires the execution-owned universe")
  let source ← metadata.node id
  let seed ← require metadata.source.layouts[source.layoutId]? "compiler layout seed"
  return ⟨id, ← layout metadata.target seed⟩

/-- Pure source-constant access. Constructed constants belong to the execution
universe and must be obtained through its checked lookup. -/
def typeConstant (metadata : RuntimeMetadata) (id : TypeConstantId) : Result MIR.TypeConst :=
  require metadata.source.typeConstants[id]? "source type constant; constructed constants require execution universe"

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
/-- Import the exact rustc contextual LayoutData by LayoutId. It contains no
type identities and requires no local layout reconstruction or World cache. -/
def layoutById (metadata : RuntimeMetadata) (id : Nat) : Result LayoutData := do
  let source ← require metadata.source.layouts[id]? "compiler layout ID out of bounds"
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
      -- Pinned rustc TyAbiInterface::ty_and_layout_field returns the same
      -- element TyAndLayout for every array/slice/str index. The row at zero
      -- is rustc's concrete result for this whole query family.
      let sourceIndex := if node.shapeKind == .str || node.shapeKind == .slice ||
          node.shapeKind == .array then 0 else index
      let source ← require (record.fields.find? (·.index == sourceIndex))
        s!"compiler projection field: parent={parent.ty}, shape={reprStr node.shapeKind}, index={index}, source_index={sourceIndex}, variants={reprStr parent.layout.variants}"
      let id := source.typeId
      let _ ← metadata.node id
      return ← projectionLayout metadata id source.layoutId
  throw (.unsupported "missing exact rustc contextual field layout result")

/-- Reconstructs precisely `LayoutData::for_variant` in pinned
rustc_abi/layout/simple.rs:158–185. Missing uninhabited-variant compiler queries
remain obligations instead of fabricated field metadata. -/
def forVariant (metadata : RuntimeMetadata) (parent : TyAndLayout TypeId) (index : Nat) :
    Result (TyAndLayout TypeId) := do
  let _ ← metadata.node parent.ty
  for record in ← projectionParents metadata parent.ty do
    if record.variant == some index then
      let canonical ← metadata.lookup parent.ty
      unless canonical == parent do
        match parent.layout.variants with
        | .Single actual =>
          if actual == index then return parent
          throw (.invalid "compiler variant projection" "cannot apply for_variant twice to a selected parent")
        | _ => throw (.invalid "compiler variant projection" "parent differs from exact rustc layout")
      return ← projectionLayout metadata parent.ty record.layoutId
  throw (.unsupported "missing exact rustc contextual variant layout result")

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

/-- Read-only constructor classification; this operation never interns a type. -/
def shapeKindInWorld (_metadata : RuntimeMetadata) (id : TypeId) : TypeArena.WorldM TypeShapeKind := do
  lift ((← get).shapeKind id)

def packedAlignInWorld (_metadata : RuntimeMetadata) (id : TypeId) : TypeArena.WorldM (Option Align) := do
  let world ← get
  let packed ← match ← lift (world.lookupType id) with
    | .material node => match node.shape with
      | .adt data => pure data.representation.packBytes
      | _ => pure none
    | .constructed (.adt ..) => do
      let (declaration,_,_,_,_) ← worldAdt id
      pure declaration.representation.packBytes
    | _ => pure none
  lift (packed.mapM (fun value => (alignment value).mapError toString))

/-- Raw coroutine source selection in the execution-owned type universe. -/
private def coroutineSourceInWorld (metadata : RuntimeMetadata) (id : TypeId) :
    TypeArena.WorldM CoroutineSourceInstantiation.Result := do
  let world ← get
  let fuel := metadata.materialLayoutFuel + 3 * (world.constructedTypes.size + world.constructedConstants.size)
  let some coverage := metadata.source.coroutineCoverage | throw "coroutine source catalog absent"
  let term ← lift (GenericInstantiationWorld.ofType world fuel id)
  lift (CoroutineSourceInstantiation.instantiate coverage.genericSources fuel term)

section EffectfulFields
variable {m : Type → Type} [Monad m] [MonadStateOf TypeArena.World m]
  [MonadExceptOf String m] [MonadLiftT (Except String) m]
  [MonadLiftT TypeArena.WorldM m]

private def coroutineFieldTypeEffectful (normalization : LayoutNormalization m) (metadata : RuntimeMetadata) (id variant index : Nat) :
    m TypeId := do
  let source ← coroutineSourceInWorld metadata id
  let term ← lift (source.stateField variant index)
  let world ← get
  let fuel := metadata.materialLayoutFuel + 3 * (world.constructedTypes.size + world.constructedConstants.size)
  normalization.resolve (fuel * (fuel + 1)) fuel term

/-- Constructor field selection may instantiate and intern raw ADT field types
in the same execution universe. The requested variant is explicit. -/
def fieldTypeEffectfulInWorld (normalization : LayoutNormalization m) (_metadata : RuntimeMetadata) (id variant index : Nat) : m TypeId := do
  let world ← get
  let fuel := _metadata.materialLayoutFuel + 3 * (world.constructedTypes.size + world.constructedConstants.size)
  match ← lift (world.lookupType id) with
  | .material node => match node.shape with
    | .coroutine .. => coroutineFieldTypeEffectful normalization _metadata id variant index
    | .closure .. | .coroutineClosure .. => do
      let fields ← worldClosureFields id
      let some field := fields[index]? | throw "capture field index absent"
      pure field
    | .adt .. =>
      worldAdtField (some normalization) fuel id variant index
    | .tuple elements =>
      let some field := elements[index]? | throw "source tuple field index absent"
      pure field
    | .array element .. | .slice element => pure element
    | .str => TypeArena.World.internType (.integer false .u8)
    | .patternType base _ =>
      unless index == 0 do throw "source pattern has only its base field"
      pure base
    | _ => throw "source type field constructor is not implemented"
  | .constructed key => match key with
    | .coroutine .. => coroutineFieldTypeEffectful normalization _metadata id variant index
    | .closure .. | .coroutineClosure .. => do
      let fields ← worldClosureFields id
      let some field := fields[index]? | throw "capture field index absent"
      pure field
    | .adt .. =>
      worldAdtField (some normalization) fuel id variant index
    | .tuple elements =>
      let some field := elements[index]? | throw "constructed tuple field index absent"
      pure field
    | .array element _ | .slice element => pure element
    | .str => TypeArena.World.internType (.integer false .u8)
    | .patternType base _ =>
      unless index == 0 do throw "constructed pattern has only its base field"
      pure base
    | _ => throw "constructed type field constructor is not implemented"

end EffectfulFields

def fieldTypeInWorld (metadata : RuntimeMetadata) (id variant index : Nat) : TypeArena.WorldM TypeId :=
  fieldTypeEffectfulInWorld (pureLayoutNormalization metadata.normalizationContext) metadata id variant index

def metadataTailInWorld (metadata : RuntimeMetadata) (id : TypeId) : TypeArena.WorldM TypeId := do
  let world ← get
  WorldTypeMetadata.metadataTail {
    normalization := metadata.normalizationContext
    unitType := metadata.source.queries.primitives.unit
    usizeType := metadata.source.queries.primitives.usize
    fieldType := fieldTypeInWorld metadata }
    (metadata.materialLayoutFuel + 3 * world.constructedTypes.size + 1) id

def pointerMetadataTypeInWorld (metadata : RuntimeMetadata) (id : TypeId) : TypeArena.WorldM TypeId := do
  let world ← get
  WorldTypeMetadata.pointerMetadataType {
    normalization := metadata.normalizationContext
    unitType := metadata.source.queries.primitives.unit
    usizeType := metadata.source.queries.primitives.usize
    fieldType := fieldTypeInWorld metadata }
    (metadata.materialLayoutFuel + 3 * world.constructedTypes.size + 1) id

/-- layout.rs917-960 maps normalized DynMetadata<dyn Trait> back to the
source vtable reference type, not to the opaque DynMetadata wrapper. -/
private def vtableFieldTypeInWorld (metadata : RuntimeMetadata) (metadataType : TypeId) :
    TypeArena.WorldM (Option TypeId) := do
  unless (← shapeKindInWorld metadata metadataType) == .adt do return none
  let (declaration,_,_,_,_) ← worldAdt metadataType
  unless declaration.langItem == some "dyn_metadata" do return none
  let .adt _ arguments ← worldConstructor metadataType | throw "DynMetadata source constructor mismatch"
  let some (Miri.MIR.GenericArg.Type dynamic) := arguments[0]? | throw "DynMetadata source type argument absent"
  let world ← get
  let fuel := metadata.materialLayoutFuel + 3 * (world.constructedTypes.size + world.constructedConstants.size)
  let some view ← lift (SourceDynamicView.query metadata.normalizationContext fuel world dynamic) | return none
  let principal := view.principal.map (fun predicate => predicate.body.definition)
  let count ← lift (SourceDynMethods.minimumEntries metadata.normalizationContext (fuel * (fuel + 1)) fuel principal)
  let bytes := metadata.target.pointerSize.bytes.toNat
  unless count < 2^(8*bytes) do throw "vtable minimum length exceeds target usize"
  let usize ← TypeArena.World.internType (.integer false .usize)
  let length ← TypeArena.World.internConstant (.Value usize ⟨#[.Leaf count bytes],0⟩)
  let array ← TypeArena.World.internType (.array usize length)
  let reference ← TypeArena.World.internType (.reference array .Not .Static)
  -- The pinned layout_of boundary normalizes/erases the constructed static region.
  some <$> WorldNormalization.normalizeType metadata.normalizationContext (fuel * (fuel + 1)) fuel reference

private def worldProjection (metadata : RuntimeMetadata) (ty : TypeId) (layoutId : LayoutId) :
    TypeArena.WorldM (TyAndLayout TypeId) := do
  let world ← get
  pure ⟨ty, ← (worldLayoutSeed (some (pureLayoutNormalization metadata.normalizationContext)) metadata.target metadata.source.layouts
    ((metadata.source.coroutineCoverage.map (·.genericSources)).getD #[])
    (metadata.materialLayoutFuel + 3 * (world.constructedTypes.size + world.constructedConstants.size)) layoutId).run' {}⟩

/- Preserve the exact selected-parent field contract for material residual
projection categories. Constructor fields use source substitution directly. -/
section EffectfulProjection
variable {m : Type → Type} [Monad m] [MonadStateOf TypeArena.World m]
  [MonadExceptOf String m] [MonadLiftT (Except String) m]
  [MonadLiftT TypeArena.WorldM m]

/-- Pointer metadata tail fields normalize in the same effectful source query.
No separate World is reconstructed and no pure alias callback is installed. -/
def pointerMetadataTypeEffectfulInWorld (normalization : LayoutNormalization m)
    (metadata : RuntimeMetadata) (id : TypeId) : m TypeId := do
  let world ← get
  WorldTypeMetadata.pointerMetadataTypeEffectful {
    normalizeType := fun fuel child => do
      let term ← lift (GenericInstantiationWorld.ofType (← get) fuel child)
      normalization.resolve (fuel * (fuel + 1)) fuel term
    unitType := metadata.source.queries.primitives.unit
    usizeType := metadata.source.queries.primitives.usize
    fieldType := fieldTypeEffectfulInWorld normalization metadata }
    (metadata.materialLayoutFuel + 3 * world.constructedTypes.size + 1) id

def fieldLayoutForEffectfulInWorld (_normalization : LayoutNormalization m) (metadata : RuntimeMetadata)
    (parent : TyAndLayout TypeId) (index : Nat) : m (TyAndLayout TypeId) := do
  let actual ← match ← lift ((← get).lookupType parent.ty) with
    | .material node => pure node
    | .constructed _ => throw "constructed type has no rustc contextual field layout result"
  let some original := metadata.source.types[parent.ty]?
    | throw "contextual field layout type is absent from rustc export"
  unless actual.id == parent.ty && actual.layoutId == original.layoutId &&
      (← lift ((← get).materialKey actual)) == (← lift ((← get).materialKey original)) do
    throw "contextual field layout type differs from rustc export"
  lift ((metadata.field parent index).mapError toString)

def fieldLayoutEffectfulInWorld (normalization : LayoutNormalization m) (metadata : RuntimeMetadata) (id index : Nat) :
    m (TyAndLayout TypeId) := do
  let parent ← layoutEffectfulInWorld normalization metadata id
  fieldLayoutForEffectfulInWorld normalization metadata parent index

end EffectfulProjection

def fieldLayoutForInWorld (metadata : RuntimeMetadata) (parent : TyAndLayout TypeId) (index : Nat) :
    TypeArena.WorldM (TyAndLayout TypeId) :=
  fieldLayoutForEffectfulInWorld (pureLayoutNormalization metadata.normalizationContext) metadata parent index

def fieldLayoutInWorld (metadata : RuntimeMetadata) (id index : Nat) : TypeArena.WorldM (TyAndLayout TypeId) :=
  fieldLayoutEffectfulInWorld (pureLayoutNormalization metadata.normalizationContext) metadata id index

/-- Raw nominal attributes; no physical layout or fields are computed. -/
def adtDeclarationInWorld (_metadata : RuntimeMetadata) (id : TypeId) :
    TypeArena.WorldM AdtDeclaration.Material := do
  let (declaration,_,_,_,_) ← worldAdt id
  pure declaration

/-- Pinned ty/layout.rs803-850 and rustc_abi/layout/simple.rs132-185.
Multiple variants are projected directly from the supplied source layout.
Single/Empty canonical enums can reconstruct pruned variants from raw ADT
field counts; applying a different variant to an already selected Multiple
layout is rejected. Contextual LayoutIds never stand in for this operation. -/
def variantLayoutInWorld (metadata : RuntimeMetadata) (parent : TyAndLayout TypeId) (index : Nat) :
    TypeArena.WorldM (TyAndLayout TypeId) := do
  let actual ← match ← lift ((← get).lookupType parent.ty) with
    | .material node => pure node
    | .constructed _ => throw "constructed type has no rustc contextual variant layout result"
  let some original := metadata.source.types[parent.ty]?
    | throw "contextual variant layout type is absent from rustc export"
  unless actual.id == parent.ty && actual.layoutId == original.layoutId &&
      (← lift ((← get).materialKey actual)) == (← lift ((← get).materialKey original)) do
    throw "contextual variant layout type differs from rustc export"
  lift ((metadata.forVariant parent index).mapError toString)

/-- Exact monomorphic Sized dispatch in the current universe after erasing
regions and normalizing the requested source type. -/
def sizedInWorld (metadata : RuntimeMetadata) (id : TypeId) : TypeArena.WorldM Bool := do
  let world ← get
  let fuel := metadata.materialLayoutFuel + 3 * (world.constructedTypes.size + world.constructedConstants.size)
  let id ← WorldNormalization.normalizeType metadata.normalizationContext (fuel * (fuel + 1)) fuel id
  worldSized (some (pureLayoutNormalization metadata.normalizationContext)) fuel id

/-- Canonical source Value extraction, never a summarized normalized answer. -/
def arrayCountInWorld (metadata : RuntimeMetadata) (id : TypeId) : TypeArena.WorldM UInt64 := do
  let world ← get
  let (length, identity) ← match ← lift (world.lookupType id) with
    | .material node => match node.shape with
      | .array _ length identity => pure (length,identity)
      | _ => throw "array count source is not an array"
    | .constructed (.array _ length) =>
      let value ← lift (world.lookupConstant length)
      let .Value _ tree := value | throw "array length requires source constant evaluation"
      let some (Miri.MIR.ValTreeNode.Leaf bits _) := tree.nodes[tree.root]?
        | throw "array length source value is not a scalar"
      pure (length,⟨bits,true⟩)
    | _ => throw "array count constructor is not an array"
  worldArrayCount metadata.target length identity

end RuntimeMetadata
end Miri.Input
