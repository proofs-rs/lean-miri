import Miri.Input.ValidateAllocIdWorld
import Miri.Input.Model.Types
import Miri.Input.Model.Catalogs
import Miri.Input.JsonReader
import Miri.Input.CompilerExternAbi
import Miri.Input.InstanceKindCodec
import Miri.Input.GenericArgsCodec

namespace Miri.Input.DecoderValues

open Lean

def expectedMiriCommit : String := "7fa591d7d4dd9af8154becbc8332f8096f8323b1"
def expectedRustcCommit : String := "8144389c895da997dbdecaa635e41d6a50be6ffd"
def expectedSchema : String := "lean-miri-rustc-mir"
def expectedSchemaVersion : Nat := 4
def expectedCompilerAbiLayoutSchema : String := "physical_ty_and_layout_v1"

def escapePathKey (key : String) : String :=
  key.toList.foldl (fun out char => out ++ match char with
    | '%' => "%25"
    | '\\' => "%5C"
    | '.' => "%2E"
    | '[' => "%5B"
    | ']' => "%5D"
    | _ => String.ofList [char]) ""

def joinPath (path key : String) : String :=
  let key := escapePathKey key
  if path.isEmpty then key else path ++ "." ++ key

def field (j : JsonReader.Slice) (key path : String) : Except String JsonReader.Slice := do
  j.field key |>.mapError fun e => s!"{path}: missing/invalid field `{key}` ({e})"

def fieldNat (j : JsonReader.Slice) (key path : String) : Except String Nat := do
  let v ← field j key path
  v.natural |>.mapError fun e => s!"{joinPath path key}: expected unsigned integer ({e})"

def fieldString (j : JsonReader.Slice) (key path : String) : Except String String := do
  let v ← field j key path
  v.string |>.mapError fun e => s!"{joinPath path key}: expected string ({e})"

def fieldBool (j : JsonReader.Slice) (key path : String) : Except String Bool := do
  let v ← field j key path
  v.boolean |>.mapError fun e => s!"{joinPath path key}: expected boolean ({e})"

def arrayField (j : JsonReader.Slice) (key path : String) : Except String (Array JsonReader.Slice) := do
  let v ← field j key path
  v.array |>.mapError fun e => s!"{joinPath path key}: expected array ({e})"

def optionalNatField (j : JsonReader.Slice) (key path : String) : Except String (Option Nat) := do
  let v ← field j key path
  if v.isNull then pure none else
    (v.natural).map some |>.mapError fun e => s!"{joinPath path key}: expected unsigned integer or null ({e})"

def optionalField (j : JsonReader.Slice) (key : String) : Option JsonReader.Slice :=
  (j.field key).toOption

def optionalString (j : JsonReader.Slice) (key path : String) : Except String (Option String) := do
  match optionalField j key with
  | none => pure none
  | some value => if value.isNull then pure none else (value.string).map some |>.mapError fun e => s!"{joinPath path key}: expected string ({e})"

def objectFields (j : JsonReader.Slice) : Except String (Array (String × JsonReader.Slice)) :=
  j.object

def statusOf? (j : JsonReader.Slice) : Option String :=
  match optionalField j "status" with
  | none => none
  | some value => match value.string with | .ok text => some text | .error _ => none


def sourceDebugString (j : JsonReader.Slice) (key path : String) : Except String String := do
  let value ← field j key path
  if let .ok text := value.string then return text
  if statusOf? value != some "debug_payload" then
    throw s!"{joinPath path key}: expected string or diagnostic debug payload"
  fieldString value "rustc_debug" (joinPath path key)

def parseSourcePosition (j : JsonReader.Slice) (path : String) : Except String SourcePosition := do
  return {
    line := ← fieldNat j "line" path
    column := ← fieldNat j "column" path
  }

def parseSourceSpan (j : JsonReader.Slice) (path : String) : Except String SourceSpanData := do
  let start ← parseSourcePosition (← field j "start" path) (joinPath path "start")
  let endPos ← parseSourcePosition (← field j "end" path) (joinPath path "end")
  return {
    isDummy := ← fieldBool j "is_dummy" path
    lo := ← fieldNat j "lo" path
    hi := ← fieldNat j "hi" path
    start := start
    «end» := endPos
    context := ← sourceDebugString j "ctxt" path
    file := ← sourceDebugString j "file" path
  }

def parseSourceInfo (j : JsonReader.Slice) (path : String) : Except String SourceInfo := do
  return {
    spanId := ← fieldNat j "span" path
    scope := ← fieldNat j "scope" path
  }

def hasField (j : JsonReader.Slice) (key : String) : Bool := (j.field key).isOk

def typeShapeKind (tag : String) : Except String TypeShapeKind :=
  match tag with
  | "bool" => pure (.bool)
  | "char" => pure (.char)
  | "int" => pure (.int)
  | "uint" => pure (.uint)
  | "float" => pure (.float)
  | "adt" => pure (.adt)
  | "foreign" => pure (.foreign)
  | "str" => pure (.str)
  | "array" => pure (.array)
  | "pattern_type" => pure (.patternType)
  | "slice" => pure (.slice)
  | "raw_pointer" => pure (.rawPointer)
  | "reference" => pure (.reference)
  | "function_definition" => pure (.functionDefinition)
  | "function_pointer" => pure (.functionPointer)
  | "unsafe_binder" => pure (.unsafeBinder)
  | "dynamic_trait_object" => pure (.dynamicTraitObject)
  | "closure" => pure (.closure)
  | "coroutine_closure" => pure (.coroutineClosure)
  | "coroutine" => pure (.coroutine)
  | "never" => pure (.never)
  | "tuple" => pure (.tuple)
  | "alias" => pure (.alias)
  | other => throw s!"unrecognized typeShapeKind tag `{other}`"

def asTag? (j : JsonReader.Slice) (key : String) : Option String :=
  (j.field key >>= JsonReader.Slice.string).toOption

def isTypeRef (j : JsonReader.Slice) : Option Nat := j.natural.toOption

def isAllocationRef (j : JsonReader.Slice) : Option Nat := j.natural.toOption

def integerTypeTag (text : String) : Except String IntegerTypeTag :=
  match text with
  | "i8" => pure (.known .i8) | "i16" => pure (.known .i16) | "i32" => pure (.known .i32)
  | "i64" => pure (.known .i64) | "i128" => pure (.known .i128) | "isize" => pure (.known .isize)
  | "u8" => pure (.known .u8) | "u16" => pure (.known .u16) | "u32" => pure (.known .u32)
  | "u64" => pure (.known .u64) | "u128" => pure (.known .u128) | "usize" => pure (.known .usize)
  | other => throw s!"unrecognized integerTypeTag tag `{other}`"

def floatTypeTag (text : String) : Except String FloatTypeTag :=
  match text with
  | "f16" => pure (.f16) | "f16b" => pure (.f16b) | "f32" => pure (.f32) | "f64" => pure (.f64)
  | "f128" => pure (.f128) | "ppcf128" => pure (.ppcf128)
  | other => throw s!"unrecognized floatTypeTag tag `{other}`"

def adtKindTag (text : String) : Except String AdtKind :=
  match text with
  | "struct" => pure (.structKind)
  | "union" => pure (.unionKind)
  | "enum" => pure (.enumKind)
  | other => throw s!"unrecognized adtKindTag tag `{other}`"

def binOpFromExportTag (tag : String) : Option Miri.MIR.BinOp :=
  match tag with
  | "add" => some .Add | "add_unchecked" => some .AddUnchecked
  | "add_with_overflow" => some .AddWithOverflow
  | "sub" => some .Sub | "sub_unchecked" => some .SubUnchecked
  | "sub_with_overflow" => some .SubWithOverflow
  | "mul" => some .Mul | "mul_unchecked" => some .MulUnchecked
  | "mul_with_overflow" => some .MulWithOverflow
  | "div" => some .Div | "rem" => some .Rem
  | "bit_xor" => some .BitXor | "bit_and" => some .BitAnd | "bit_or" => some .BitOr
  | "shift_left" => some .Shl | "shift_left_unchecked" => some .ShlUnchecked
  | "shift_right" => some .Shr | "shift_right_unchecked" => some .ShrUnchecked
  | "equal" => some .Eq | "less_than" => some .Lt | "less_equal" => some .Le
  | "not_equal" => some .Ne | "greater_equal" => some .Ge | "greater_than" => some .Gt
  | "compare" => some .Cmp | "pointer_offset" => some .Offset
  | _ => Miri.MIR.BinOp.ofString tag

def unOpFromExportTag (tag : String) : Option Miri.MIR.UnOp :=
  match tag with
  | "not" => some .Not
  | "negate" => some .Neg
  | "pointer_metadata" => some .PtrMetadata
  | _ => Miri.MIR.UnOp.ofString tag

def jsonArray (j : JsonReader.Slice) (path : String) : Except String (Array JsonReader.Slice) :=
  j.array |>.mapError fun e => s!"{path}: expected array ({e})"

def natArray (j : JsonReader.Slice) (path : String) : Except String (Array Nat) := do
  let values ← jsonArray j path
  let mut out := #[]
  let mut index := 0
  for value in values do
    out := out.push (← value.natural |>.mapError fun e => s!"{path}[{index}]: expected unsigned integer ({e})")
    index := index + 1
  return out

def optionalNat (j : JsonReader.Slice) (key path : String) : Except String (Option Nat) := do
  match optionalField j key with
  | none => pure none
  | some value => if value.isNull then pure none else (value.natural).map some |>.mapError fun e => s!"{joinPath path key}: expected unsigned integer or null ({e})"

def optionalJson (j : JsonReader.Slice) (key : String) : Option JsonReader.Slice :=
  optionalField j key |>.filter (!·.isNull)

def parseTagged (j : JsonReader.Slice) (path : String) : Except String TaggedNode := do
  let tag ← fieldString j "kind" path
  return ⟨tag⟩

def parseAbiTag (j : JsonReader.Slice) (path : String) : Except String TaggedNode := do
  if let .ok tag := j.string then return ⟨tag⟩
  let tag ← match optionalField j "kind" with
    | some value => value.string
    | none => match optionalField j "variant" with
      | some value => value.string
      | none => throw s!"{path}: enum object is missing its kind tag"
  return ⟨tag⟩

def layoutVariantsKind (tag : String) : Except String LayoutVariantsKind :=
  match tag with
  | "single" => pure (.single)
  | "multiple" => pure (.multiple)
  | "empty" => pure (.empty)
  | other => throw s!"unrecognized layoutVariantsKind tag `{other}`"

def backendReprKind (tag : String) : Except String BackendReprKind :=
  match tag with
  | "scalar" => pure (.scalar)
  | "scalar_pair" => pure (.scalarPair)
  | "memory" => pure (.memory)
  | "simd_vector" => pure (.simdVector)
  | "scalable_simd_vector" => pure (.scalableSimdVector)
  | other => throw s!"unrecognized backendReprKind tag `{other}`"

def optionalNatBefore (j : JsonReader.Slice) (key path : String) : Except String (Option Nat) := do
  match optionalField j key with
  | none => pure none
  | some value => if value.isNull then pure none else (value.natural).map some |>.mapError fun e => s!"{joinPath path key}: expected unsigned integer or null ({e})"

def parsePrimitiveLayout (j : JsonReader.Slice) (path : String) : Except String PrimitiveLayout := do
  let tag ← fieldString j "kind" path
  let kind : PrimitiveKind ← match tag with
    | "integer" => pure (.integer)
    | "float" => pure (.float)
    | "pointer" => pure (.pointer)
    | other => throw s!"{path}: unrecognized PrimitiveKind `{other}`"
  let integerKindText ← optionalString j "integer_kind" path
  let integerKind ← integerKindText.mapM integerTypeTag
  let signed ← match optionalField j "signed" with
    | none => pure none
    | some value => if value.isNull then pure none else (value.boolean).map some |>.mapError fun e => s!"{joinPath path "signed"}: expected boolean ({e})"
  let floatKindText ← optionalString j "float_kind" path
  let floatKind ← floatKindText.mapM floatTypeTag
  let addressSpace ← optionalNatBefore j "address_space" path
  return {
    kind := kind
    sizeBytes := ← fieldNat j "size_bytes" path
    integerKind := integerKind
    signed := signed
    floatKind := floatKind
    addressSpace := addressSpace
  }

def parseU128Natural (j : JsonReader.Slice) (path : String) : Except String Nat := do
  let text ← j.string |>.mapError fun error => s!"{path}: expected exact unsigned decimal string ({error})"
  unless !text.isEmpty && text.toList.all Char.isDigit do throw s!"{path}: expected exact unsigned decimal string"
  let some value := text.toNat? | throw s!"{path}: invalid unsigned decimal"
  unless value < 2^128 do throw s!"{path}: u128 overflow"
  pure value

def parseScalarLayout (j : JsonReader.Slice) (path : String) : Except String ScalarLayout := do
  let tag ← fieldString j "kind" path
  let kind : ScalarShapeKind ← match tag with
    | "initialized" => pure (.initialized)
    | "union" => pure (.union)
    | other => throw s!"{path}: unrecognized ScalarShapeKind `{other}`"
  let range ← match optionalJson j "valid_range" with
    | none => pure none
    | some value => pure (some (← parseU128Natural (← field value "start" (joinPath path "valid_range")) (joinPath path "valid_range.start"), ← parseU128Natural (← field value "end" (joinPath path "valid_range")) (joinPath path "valid_range.end")))
  return {
    kind := kind
    primitive := ← parsePrimitiveLayout (← field j "primitive" path) (joinPath path "primitive")
    validRange := range
  }

def parseNicheLayout (j : JsonReader.Slice) (path : String) : Except String (Option NicheLayout) := do
  if j.isNull then return none
  let range ← field j "valid_range" path
  return some {
    offsetBytes := ← fieldNat j "offset_bytes" path
    primitive := ← parsePrimitiveLayout (← field j "primitive" path) (joinPath path "primitive")
    validRange := (← parseU128Natural (← field range "start" (joinPath path "valid_range")) (joinPath path "valid_range.start"),
      ← parseU128Natural (← field range "end" (joinPath path "valid_range")) (joinPath path "valid_range.end"))
  }

def parseBackendRepr (j : JsonReader.Slice) (path : String) : Except String BackendRepr := do
  let tag ← fieldString j "kind" path
  let kind ← backendReprKind tag
  let scalar ← match optionalJson j "scalar" with
    | none => pure none
    | some value => pure (some (← parseScalarLayout value (joinPath path "scalar")))
  let first ← match optionalJson j "first" with
    | none => pure none
    | some value => pure (some (← parseScalarLayout value (joinPath path "first")))
  let second ← match optionalJson j "second" with
    | none => pure none
    | some value => pure (some (← parseScalarLayout value (joinPath path "second")))
  let element ← match optionalJson j "element" with
    | none => pure none
    | some value => pure (some (← parseScalarLayout value (joinPath path "element")))
  let sized ← match optionalField j "sized" with
    | none => pure none
    | some value => if value.isNull then pure none else (value.boolean).map some |>.mapError fun e => s!"{joinPath path "sized"}: expected boolean ({e})"
  let secondOffsetBytes ← optionalNatBefore j "second_offset_bytes" path
  let laneCount ← optionalNatBefore j "lane_count" path
  let vectorCount ← optionalNatBefore j "vector_count" path
  match kind with
  | .scalar => if scalar.isNone then throw s!"{path}: scalar backend representation is missing scalar data"
  | .scalarPair =>
    if first.isNone || second.isNone || secondOffsetBytes.isNone then
      throw s!"{path}: scalar-pair backend representation is incomplete"
  | .memory => if sized.isNone then throw s!"{path}: memory backend representation is missing `sized`"
  | .simdVector | .scalableSimdVector =>
    if element.isNone || laneCount.isNone then throw s!"{path}: SIMD backend representation is incomplete"
  return {
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

def parseFieldShape (j : JsonReader.Slice) (path : String) : Except String FieldShape := do
  let tag ← fieldString j "kind" path
  let kind : FieldShapeKind ← match tag with
    | "primitive" => pure (.primitive)
    | "union" => pure (.union)
    | "array" => pure (.array)
    | "arbitrary" => pure (.arbitrary)
    | other => throw s!"{path}: unrecognized FieldShapeKind `{other}`"
  let fieldCount ← optionalNatBefore j "field_count" path
  let offsetBytes ← optionalNatBefore j "offset_bytes" path
  let strideBytes ← optionalNatBefore j "stride_bytes" path
  let offsetsBytes ← match optionalJson j "offsets_bytes" with
    | none => pure #[]
    | some value => natArray value (joinPath path "offsets_bytes")
  let memoryOrder ← match optionalJson j "memory_order" with
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
  return {
    kind := kind
    fieldCount := fieldCountValue
    offsetBytes := offsetBytes
    strideBytes := strideBytes
    offsetsBytes := offsetsBytes
    memoryOrder := memoryOrder
  }

def parseLayoutVariant (j : JsonReader.Slice) (path : String) : Except String LayoutVariant := do
  return {
    fields := ← parseFieldShape (← field j "fields" path) (joinPath path "fields")
    largestNiche := ← parseNicheLayout (← field j "largest_niche" path) (joinPath path "largest_niche")
    variantIndex := ← fieldNat j "variant_index" path
    sizeBytes := ← fieldNat j "size_bytes" path
    backendRepr := ← parseBackendRepr (← field j "backend_repr" path) (joinPath path "backend_repr")
    fieldOffsetsBytes := ← natArray (← field j "field_offsets_bytes" path) (joinPath path "field_offsets_bytes")
    uninhabited := ← fieldBool j "uninhabited" path
  }

def decimalNat (text path : String) : Except String Nat := do
  if text.isEmpty then throw s!"{path}: expected a nonempty unsigned decimal integer"
  let mut value := 0
  for digit in text.toList do
    if digit < '0' || digit > '9' then throw s!"{path}: expected an unsigned decimal integer"
    value := value * 10 + digit.toNat - '0'.toNat
  return value

def parseTagEncoding (j : JsonReader.Slice) (path : String) : Except String TagEncoding := do
  let tag ← fieldString j "kind" path
  let kind : TagEncodingKind ← match tag with
    | "direct" => pure (TagEncodingKind.direct)
    | "niche" => pure (TagEncodingKind.niche)
    | other => throw s!"{path}: unrecognized TagEncodingKind `{other}`"
  let untaggedVariant ← optionalNat j "untagged_variant" path
  let nicheVariants ← match optionalJson j "niche_variants" with
    | none => pure none
    | some range => pure (some (← fieldNat range "start" (joinPath path "niche_variants"), ← fieldNat range "end" (joinPath path "niche_variants")))
  let nicheStart ← match optionalField j "niche_start" with
    | none => pure none
    | some value => if value.isNull then pure none else
      let text ← value.string |>.mapError fun e => s!"{joinPath path "niche_start"}: expected exact decimal string ({e})"
      pure (some (← decimalNat text (joinPath path "niche_start")))
  match kind with
  | .direct => pure ()
  | .niche =>
    if (untaggedVariant.isNone || nicheVariants.isNone || nicheStart.isNone) then
      throw s!"{path}: supported niche tag encoding is missing its range or start value"
  return ⟨kind, untaggedVariant, nicheVariants, nicheStart⟩

def parseVariantsLayout (j : JsonReader.Slice) (path : String) : Except String VariantsLayout := do
  let tag ← fieldString j "kind" path
  let kind ← layoutVariantsKind tag
  let variantIndex ← optionalNatBefore j "variant_index" path
  let scalarTag ← match optionalJson j "tag" with
    | none => pure none
    | some value => pure (some (← parseScalarLayout value (joinPath path "tag")))
  let tagEncoding ← match optionalJson j "tag_encoding" with
    | none => pure none
    | some value => pure (some (← parseTagEncoding value (joinPath path "tag_encoding")))
  let tagFieldIndex ← optionalNatBefore j "tag_field_index" path
  let variantsJson ← match optionalJson j "variants" with
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
  return {
    kind := kind
    variantIndex := variantIndex
    tag := scalarTag
    tagEncoding := tagEncoding
    tagFieldIndex := tagFieldIndex
    variants := variants
  }

def parseLayout (j : JsonReader.Slice) (path : String) : Except String Layout := do
  let kind : LayoutKind ← match asTag? j "kind" with
    | some "layout" | none => pure (.layout)
    | some value => throw s!"{path}: unrecognized LayoutKind `{value}`"
  let offsets ← natArray (← field j "field_offsets_bytes" path) (joinPath path "field_offsets_bytes")
  let variants ← match optionalJson j "variants" with
    | none => pure none
    | some value => pure (some (← parseTagged value (joinPath path "variants")))
  let backend ← match optionalJson j "backend_repr" with
    | none => pure none
    | some value => pure (some (← parseTagged value (joinPath path "backend_repr")))
  let fields ← match optionalJson j "fields" with
    | none => pure none
    | some value => pure (some (← parseFieldShape value (joinPath path "fields")))
  let variantsLayout ← match optionalJson j "variants" with
    | none => pure none
    | some value => pure (some (← parseVariantsLayout value (joinPath path "variants")))
  let backendRepresentation ← match optionalJson j "backend_repr" with
    | none => pure none
    | some value => pure (some (← parseBackendRepr value (joinPath path "backend_repr")))
  let sizeBytes ← optionalNat j "size_bytes" path
  let abiAlignBytes ← optionalNat j "abi_align_bytes" path
  let unadjustedAbiAlignBytes ← optionalNat j "unadjusted_abi_align_bytes" path
  let variantsKind ← variants.mapM fun value => layoutVariantsKind value.tag
  let backendReprKind ← backend.mapM fun value => backendReprKind value.tag
  if (sizeBytes.isNone || abiAlignBytes.isNone || unadjustedAbiAlignBytes.isNone) then
    throw s!"{path}: supported layout is missing size/alignment fields"
  if (fields.isNone || variantsLayout.isNone || backendRepresentation.isNone) then
    throw s!"{path}: supported layout is missing field/variant/backend representation data"
  match fields with
  | some fieldShape =>
    if fieldShape.fieldCount != offsets.size then
      throw s!"{path}: field shape count does not match field_offsets_bytes"
  | none => pure ()
  return {
    maxReprAlignBytes := ← optionalNatField j "max_repr_align_bytes" path
    reprC := ← fieldBool j "repr_c" path
    uninhabited := ← fieldBool j "uninhabited" path
    largestNiche := ← parseNicheLayout (← field j "largest_niche" path) (joinPath path "largest_niche")
    randomizationSeed := ← fieldNat j "randomization_seed" path
    kind := kind
    sizeBytes := sizeBytes
    abiAlignBytes := abiAlignBytes
    unadjustedAbiAlignBytes := unadjustedAbiAlignBytes
    fieldOffsetsBytes := offsets
    fields := fields
    variantsLayout := variantsLayout
    backendRepresentation := backendRepresentation
    variantsKind := variantsKind
    backendReprKind := backendReprKind
    variants := variants
    backendRepr := backend
  }

def parseFunctionSignature (j : JsonReader.Slice) (path : String) : Except String FunctionSignature := do
  let inputsJson ← arrayField j "inputs" path
  let mut inputs := #[]
  let mut index := 0
  for input in inputsJson do
    let id ← match isTypeRef input with
      | some id => pure id
      | none => throw s!"{joinPath path "inputs"}[{index}]: expected type reference"
    inputs := inputs.push id
    index := index + 1
  let outputJson ← field j "output" path
  let output ← match isTypeRef outputJson with
    | some id => pure id
    | none => throw s!"{joinPath path "output"}: expected type reference"
  let safetyTag ← parseAbiTag (← field j "safety" path) (joinPath path "safety")
  let safety ← match safetyTag.tag with
    | "safe" => pure Miri.MIR.Safety.Safe
    | "unsafe" => pure .Unsafe
    | _ => throw s!"{path}: unknown function signature safety"
  return {
    inputs, output, safety
    abi := ← CompilerExternAbi.decode (← field j "abi" path)
    cVariadic := ← fieldBool j "c_variadic" path
  }

def decodeCompilerPredicateEvidence (j : JsonReader.Slice) : Except String CompilerPredicateEvidence := do
  let normalization ← field j "normalization" "$predicate"
  let normalized ← if normalization.isNull then pure none else normalization.natural.map some
  pure {
    id := ← fieldNat j "predicate_id" "$predicate"
    typingEnvironment := ← fieldString j "typing_env" "$predicate"
    stableKey := ← fieldNat j "stable_key" "$predicate"
    autoTrait := ← fieldBool j "auto_trait" "$predicate"
    normalizedId := normalized
    original := ← fieldNat j "original" "$predicate" }


/-- Decode all source PatternKind branches; unknown kinds fail explicitly. -/
partial def decodeCompilerPattern (j : JsonReader.Slice) : Except String CompilerPattern := do
  match ← fieldString j "kind" "$pattern" with
  | "range" => return .range (← fieldNat j "start" "$pattern") (← fieldNat j "end" "$pattern")
  | "or" => return .or (← (← arrayField j "patterns" "$pattern").mapM decodeCompilerPattern)
  | "not_null" => pure .notNull
  | _ => throw "unknown compiler PatternKind"

private def parseProjectionQueries (j : JsonReader.Slice) (path : String) : Except String ProjectionQueries := do
  let parents ← (← arrayField j "parents" path).mapM fun parent => do
    let fields ← (← arrayField parent "fields" path).mapM fun value => do
      let index ← fieldNat value "index" path
      let typeId ← fieldNat value "type" path
      let layoutId ← fieldNat value "layout" path
      pure ({ index, typeId, layoutId } : ProjectionField)
    let variant ← optionalNat parent "variant" path
    let layoutId ← fieldNat parent "layout" path
    pure ({ variant, layoutId, fields } : ProjectionParent)
  let typingEnvironment ← fieldString j "typing_env" path
  pure { typingEnvironment, parents }

private def parseDiscriminants (j : JsonReader.Slice) (path : String) : Except String DiscriminantInfo := do
  let values ← (← arrayField j "values" path).mapM fun value => do
    let variant ← fieldNat value "variant" path
    unless variant < 2^32 do throw s!"{path}: compiler variant index exceeds u32"
    let bits ← decimalNat (← fieldString value "bits" path) path
    unless bits < 2^128 do throw s!"{path}: compiler discriminant exceeds u128"
    let typeId ← fieldNat value "type" path
    pure ({ variant, typeId, bits } : DiscriminantValue)
  let hasDiscriminants ← fieldBool j "has_discriminants" path
  let adtVariantCount ← optionalNat j "adt_variant_count" path
  pure { hasDiscriminants, adtVariantCount, values }

/-- Preserve the compiler query's exact type and typing-environment key. -/
def decodeTypeCompilerFacts (j : JsonReader.Slice) (path : String := "$compiler_facts") : Except String TypeCompilerFacts := do
  let some inputType := isTypeRef (← field j "input_type" path) | throw "compiler fact input_type is not a type reference"
  let mut booleans := #[]
  for (name,value) in ← objectFields (← field j "boolean_queries" path) do
    let result ← value.boolean
    booleans := booleans.push (name, result)
  let mut types := #[]
  for (name,value) in ← objectFields (← field j "type_queries" path) do
    let result ← do
      if value.isNull then pure none else match isTypeRef value with
      | some id => pure (some id)
      | none => throw "compiler type query value is not a type reference or null"
    types := types.push (name, result)
  let captureNames ← match optionalField j "capture_names" with
    | none => pure none
    | some query =>
      if query.isNull then pure none else
        some <$> ((← query.array).mapM fun name =>
          if name.isNull then pure none else name.string.map some)
  let adt ← do
    let value ← field j "adt" path
    if value.isNull then pure none else do
      let definitionId ← fieldNat value "definition" path
      let itemName ← fieldString value "item_name" path
      let nonnullOptimizationGuaranteed ← fieldBool value "nonnull_optimization_guaranteed" path
      pure (some ({ definitionId, itemName, nonnullOptimizationGuaranteed } : AdtCompilerFacts))
  let projectionQueries ← do
    let value ← field j "projection_queries" path
    if value.isNull then pure none else some <$> parseProjectionQueries value (joinPath path "projection_queries")
  let simdSizeAndType : Option (Nat × TypeId) ← do
    let value ← field j "simd_size_and_type" path
    if value.isNull then pure none else do
      let count ← fieldNat value "count" path
      unless count < 2^64 do throw s!"{path}: SIMD lane count exceeds u64"
      let element ← fieldNat value "element" path
      pure (some (count, element))
  let discriminants ← do
    let value ← field j "discriminants" path
    if value.isNull then pure none else some <$> parseDiscriminants value (joinPath path "discriminants")
  let typeIdHash ← match optionalField j "type_id_hash" with
    | none => pure none
    | some value => do
      let bits ← decimalNat (← value.string) (joinPath path "type_id_hash")
      unless bits < 2^128 do throw s!"{path}: compiler TypeId hash exceeds u128"
      pure (some bits)
  pure {
    captureNames := captureNames,
    typingEnvironment := ← fieldString j "typing_env" path, inputTypeId := inputType,
    queryInputTypeId := ← fieldNat j "query_input_type" path,
    booleanQueries := booleans, typeQueries := types,
    adt, projectionQueries, simdSizeAndType, discriminants, typeIdHash,
    definitionId := ← optionalNat j "definition" path,
    }

private def parseReprOptions (j : JsonReader.Slice) (path : String) : Except String ReprOptions := do
  let integer ← do
    let value ← field j "integer" path
    if value.isNull then pure none else do
      let result ← match ← fieldString value "kind" path with
        | "pointer_sized" => do
          pure (ReprInteger.pointerSized (← fieldBool value "signed" path))
        | "fixed" => do
          pure (ReprInteger.fixed (← integerTypeTag (← fieldString value "integer_kind" path))
            (← fieldNat value "size_bits" path) (← fieldBool value "signed" path))
        | _ => throw s!"{path}.integer: unknown representation integer"
      pure (some result)
  let scalableElement ← do
    let value ← field j "scalable_element" path
    if value.isNull then pure none else do
      let result ← match ← fieldString value "kind" path with
        | "element_count" => do
          pure (ScalableElement.elementCount (← fieldNat value "count" path))
        | "container" => pure ScalableElement.container
        | _ => throw s!"{path}.scalable_element: unknown scalable representation"
      pure (some result)
  return {
    integer := integer
    alignBytes := ← optionalNatField j "align_bytes" path
    packBytes := ← optionalNatField j "pack_bytes" path
    simd := ← fieldBool j "simd" path
    c := ← fieldBool j "c" path
    rust := ← fieldBool j "rust" path
    packed := ← fieldBool j "packed" path
    transparent := ← fieldBool j "transparent" path
    linear := ← fieldBool j "linear" path
    scalable := ← fieldBool j "scalable" path
    flagsBits := ← fieldNat j "flags_bits" path
    scalableElement := scalableElement
    canRandomizeTypeLayout := ← fieldBool j "can_randomize_type_layout" path
    inhibitEnumLayoutOptimization := ← fieldBool j "inhibit_enum_layout_optimization" path
    inhibitStructFieldReordering := ← fieldBool j "inhibit_struct_field_reordering" path
    inhibitNewtypeAbiOptimization := ← fieldBool j "inhibit_newtype_abi_optimization" path
    fieldShuffleSeed := ← fieldNat j "field_shuffle_seed" path }

private def parseAdtShape (j : JsonReader.Slice) (path : String) : Except String AdtShape := do
  let variants ← (← arrayField j "variants" path).mapIdxM fun index variant => do
    let p := s!"{path}.variants[{index}]"
    let fields ← (← arrayField variant "fields" p).mapIdxM fun fieldIndex f => do
      let fp := s!"{p}.fields[{fieldIndex}]"
      let id ← fieldNat f "index" fp
      unless id == fieldIndex do throw s!"{fp}.index: field/index mismatch"
      let name ← fieldString f "name" fp
      let typeId ← fieldNat f "type" fp
      pure (AdtField.mk id name typeId)
    let id ← fieldNat variant "index" p
    unless id == index do throw s!"{p}.index: variant/index mismatch"
    let name ← fieldString variant "name" p
    pure (AdtVariant.mk id name fields)
  return {
    definition := ← fieldNat j "def_id" path
    kind := ← adtKindTag (← fieldString j "adt_kind" path)
    representation := ← parseReprOptions (← field j "representation" path) (joinPath path "representation")
    args := ← GenericArgsCodec.decode (← field j "generic_args" path)
    variants := variants }

private def parseShapeMutability (j : JsonReader.Slice) (path : String) : Except String Miri.MIR.Mutability := do
  match ← fieldString j "kind" path with
  | "mutable" => pure .Mut
  | "immutable" => pure .Not
  | _ => throw s!"{path}: unknown mutability"

private def parseShapeBoundVariables (j : JsonReader.Slice) (key path : String) :
    Except String (Array Miri.MIR.BoundVariableKind) := do
  (← arrayField j key path).mapM GenericArgsCodec.boundVariable

private def parseTypeShape (j : JsonReader.Slice) (path : String) : Except String TypeShape := do
  let args := do GenericArgsCodec.decode (← field j "generic_args" path)
  let definition := fieldNat j "def_id" path
  let region := do GenericArgsCodec.region (← field j "region" path)
  let mutability := do parseShapeMutability (← field j "mutability" path) (joinPath path "mutability")
  let signature := do parseFunctionSignature (← field j "signature" path) (joinPath path "signature")
  let boundVariables := parseShapeBoundVariables j "signature_bound_variables" path
  match ← fieldString j "kind" path with
  | "bool" => pure .bool
  | "char" => pure .char
  | "int" =>
    let spelling ← fieldString j "signed_kind" path
    unless ["i8", "i16", "i32", "i64", "i128", "isize"].contains spelling do
      throw s!"{path}.signed_kind: expected signed integer kind"
    return .int (← integerTypeTag spelling)
  | "uint" =>
    let spelling ← fieldString j "unsigned_kind" path
    unless ["u8", "u16", "u32", "u64", "u128", "usize"].contains spelling do
      throw s!"{path}.unsigned_kind: expected unsigned integer kind"
    return .uint (← integerTypeTag spelling)
  | "float" => return .float (← floatTypeTag (← fieldString j "float_kind" path))
  | "adt" => return .adt (← parseAdtShape j path)
  | "foreign" => return .foreign (← definition)
  | "str" => pure .str
  | "array" =>
    let constructor ← field j "constructor_identity" path
    return .array (← fieldNat j "element" path) (← fieldNat j "length" path)
      ⟨← fieldNat constructor "count" (joinPath path "constructor_identity"),
       ← fieldBool constructor "canonical_value_constructor" (joinPath path "constructor_identity")⟩
  | "pattern_type" => do
    return .patternType (← fieldNat j "base" path) (← decodeCompilerPattern (← field j "pattern" path))
  | "slice" => return .slice (← fieldNat j "element" path)
  | "raw_pointer" => return .rawPointer (← fieldNat j "pointee" path) (← mutability)
  | "reference" => return .reference (← fieldNat j "pointee" path) (← mutability) (← region)
  | "function_definition" => return .functionDefinition (← definition) (← args) (← signature) (← boundVariables)
  | "function_pointer" => return .functionPointer (← signature) (← boundVariables)
  | "unsafe_binder" => do
    return .unsafeBinder (← fieldNat j "inner" path) (← parseShapeBoundVariables j "bound_variables" path)
  | "dynamic_trait_object" =>
    let predicates ← (← arrayField j "predicates" path).mapM JsonReader.Slice.natural
    return .dynamicTraitObject predicates (← optionalNatField j "principal_predicate" path) (← region)
  | "closure" => return .closure (← definition) (← args) (← fieldNat j "upvar_count" path)
  | "coroutine_closure" => return .coroutineClosure (← definition) (← args)
  | "coroutine" => return .coroutine (← definition) (← args)
  | "never" => pure .never
  | "tuple" => return .tuple (← (← arrayField j "elements" path).mapM JsonReader.Slice.natural)
  | "alias" =>
    let payload ← field j "alias_payload" path
    let definition ← definition
    unless (← fieldNat payload "def_id" path) == definition do throw s!"{path}: alias definition mismatch"
    let kind ← match ← fieldString payload "kind" path with
      | "Projection" => pure AliasTypeKind.projection
      | "Inherent" => pure .inherent
      | "Opaque" => pure .opaque
      | "Free" => pure .free
      | _ => throw s!"{path}: unknown alias kind"
    return .alias kind definition (← args)
  | tag => throw s!"{path}: unrecognized type shape `{tag}`"

def parseTypeNode (j : JsonReader.Slice) (path : String) : Except String TypeNode := do
  return {
    layoutQueryInputTypeId := ← optionalNatField j "layout_query_input_type" path
    compilerFacts := ← match optionalField j "compiler_facts" with
      | none => pure none
      | some value => (decodeTypeCompilerFacts value (joinPath path "compiler_facts")).map some
    id := ← fieldNat j "type_id" path
    display := ← fieldString j "display" path
    shape := ← parseTypeShape (← field j "shape" path) (joinPath path "shape")
    layoutId := ← fieldNat j "layout" path }

def hexDigit (c : Char) : Bool :=
  c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

def validHex (value : String) : Bool := value.toList.all hexDigit && value.length % 2 == 0

def parseInitRange (j : JsonReader.Slice) (path : String) : Except String InitRange := do
  let state ← fieldString j "state" path
  let initialized ← match state with
    | "initialized" => pure true
    | "uninitialized" => pure false
    | _ => throw s!"{joinPath path "state"}: unrecognized initialization state `{state}`"
  let first ← fieldNat j "start_bytes" path
  let last ← fieldNat j "end_bytes_exclusive" path
  if last < first then throw s!"{path}: initialization range has end before start"
  return ⟨initialized, first, last⟩

def parseRelocation (j : JsonReader.Slice) (path : String) : Except String Relocation := do
  let targetRef ← field j "target" path
  let target ← match isAllocationRef targetRef with
    | some id => pure id
    | none => throw s!"{joinPath path "target"}: expected allocation ID"
  -- Export IDs are zero-based and compilation-local.  The public CTFE
  -- provenance record requires a nonzero AllocId, so use the reversible +1
  -- embedding here and retain the original export ID separately in `target`.
  let leanAllocId ← match Miri.Memory.AllocId.ofUInt64 (UInt64.ofNat (target + 1)) with
    | some id => pure id
    | none => throw s!"{joinPath path "target"}: export allocation ID cannot be represented as a nonzero CTFE identity"
  let immutable ← fieldBool j "immutable" path
  let sharedRef ← fieldBool j "shared_ref" path
  let ctfeProvenance ← match Miri.Memory.CtfeProvenance.fromParts (leanAllocId, immutable, sharedRef) with
    | .ok provenance => pure provenance
    | .error _ => throw s!"{path}: invalid CTFE provenance flags or allocation-ID width"
  let encoded ← fieldString j "target_offset_encoded_bytes" path
  if !validHex encoded then throw s!"{joinPath path "target_offset_encoded_bytes"}: malformed hexadecimal bytes"
  return {
    storageOffsetBytes := ← fieldNat j "storage_offset_bytes" path
    target := target
    targetOffsetEncodedBytes := encoded
    immutable := immutable
    sharedRef := sharedRef
    ctfeProvenance := ctfeProvenance
  }

def parseAllocationMemory (j : JsonReader.Slice) (path : String) : Except String AllocationMemory := do
  let bytes ← fieldString j "bytes_hex" path
  if !validHex bytes then throw s!"{joinPath path "bytes_hex"}: malformed hexadecimal bytes"
  let rangesJson ← arrayField j "initialization_ranges" path
  let mut ranges := #[]
  let mut index := 0
  for value in rangesJson do
    ranges := ranges.push (← parseInitRange value s!"{joinPath path "initialization_ranges"}[{index}]")
    index := index + 1
  let relocJson ← arrayField j "relocations" path
  let mut relocations := #[]
  index := 0
  for value in relocJson do
    relocations := relocations.push (← parseRelocation value s!"{joinPath path "relocations"}[{index}]")
    index := index + 1
  let size := ← fieldNat j "size_bytes" path
  if bytes.length / 2 != size then throw s!"{joinPath path "bytes_hex"}: byte buffer length does not equal size_bytes"
  let mut cursor := 0
  for chunk in ranges do
    if chunk.startBytes != cursor then throw s!"{joinPath path "initialization_ranges"}: ranges overlap or leave a gap"
    if chunk.endBytesExclusive > size then throw s!"{joinPath path "initialization_ranges"}: range exceeds allocation size"
    cursor := chunk.endBytesExclusive
  if cursor != size then throw s!"{joinPath path "initialization_ranges"}: ranges do not cover the allocation"
  for relocation in relocations do
    if relocation.storageOffsetBytes + relocation.targetOffsetEncodedBytes.length / 2 > size then
      throw s!"{joinPath path "relocations"}: relocation's encoded pointer bytes exceed allocation size"
  let alignBytes ← fieldNat j "align_bytes" path
  if alignBytes == 0 then throw s!"{joinPath path "align_bytes"}: allocation alignment must be nonzero"
  return {
    sizeBytes := size
    alignBytes := alignBytes
    mutability := ← match ← fieldString j "mutability" path with
      | "mutable" => pure .mutable
      | "immutable" => pure .immutable
      | other => throw s!"{path}.mutability: unrecognized memory mutability `{other}`"
    bytesHex := bytes
    initializationRanges := ranges
    relocations := relocations
  }

def allocationKind (kind : String) : Except String AllocationKind :=
  match kind with
  | "memory" => pure (.memory)
  | "function" => pure (.function)
  | "static" => pure (.static)
  | "vtable" => pure (.vtable)
  | "type_id" => pure (.typeId)
  | "" => throw "allocation kind is missing"
  | other => throw s!"unrecognized allocationKind tag `{other}`"

def parseDefinitionId (j : JsonReader.Slice) (path : String) : Except String DefinitionId := do
  return ⟨← fieldNat j "crate" path, ← fieldNat j "index" path⟩

def parseDefinitionRef (j : JsonReader.Slice) (path : String) : Except String DefinitionRef :=
  j.natural |>.mapError fun error => s!"{path}: expected definition ID ({error})"

def parseSelectedScope (j : JsonReader.Slice) (path : String) : Except String SelectedScope := do
  let kind ← fieldString j "kind" path
  let rootsJson ← arrayField j "roots" path
  let mut roots := #[]
  for (root, index) in rootsJson.toList.zipIdx do
    let rootPath := s!"{joinPath path "roots"}[{index}]"
    let defPath ← fieldString root "def_path" rootPath
    if defPath.isEmpty then throw s!"{joinPath rootPath "def_path"}: selected root path cannot be empty"
    roots := roots.push ⟨defPath, ← parseDefinitionRef (← field root "def_id" rootPath) (joinPath rootPath "def_id")⟩
  if roots.toList.eraseDups.length != roots.size then throw s!"{joinPath path "roots"}: duplicate selected roots"
  return {
    kind := kind
    semantics := ← fieldString j "semantics" path
    roots := roots
  }

def vtablePredicateKind (tag : String) : Except String VtablePredicateKind :=
  match tag with
  | "trait" => pure (.trait)
  | "auto_trait" => pure (.autoTrait)
  | "projection" => pure (.projection)
  | other => throw s!"unrecognized vtablePredicateKind tag `{other}`"

def parseVtablePredicate (j : JsonReader.Slice) (path : String) : Except String VtablePredicate := do
  let tag ← fieldString j "kind" path
  let kind ← vtablePredicateKind tag
  let genericArgs ← if kind == .autoTrait then pure #[] else
    GenericArgsCodec.decode (← field j "generic_args" path)
  let projectionTerm ← if kind == .projection then do
    let term ← field j "term" path
    unless (← fieldString term "kind" (joinPath path "term")) == "type" do
      throw s!"{path}: unsupported predicate projection term"
    pure (some (← fieldNat term "value" (joinPath path "term")))
    else pure none
  let boundVariables ← ((← arrayField j "bound_variables" path).toList.zipIdx.mapM fun ((value, index) : JsonReader.Slice × Nat) =>
    GenericArgsCodec.boundVariable value |>.mapError fun error => s!"{path}.bound_variables[{index}]: {error}").map List.toArray
  return {
    kind
    definitionId := ← fieldNat j "def_id" path
    definitionPath := ← optionalString j "def_path" path
    genericArgs
    boundVariables
    projectionTerm
  }

def vtableEntryKind (tag : String) : Except String VtableEntryKind :=
  match tag with
  | "drop_in_place_null" => pure (.dropInPlaceNull)
  | "drop_in_place" => pure (.dropInPlace)
  | "size_bytes" => pure (.sizeBytes)
  | "align_bytes" => pure (.alignBytes)
  | "vacant" => pure (.vacant)
  | "method" => pure (.method)
  | "supertrait_vtable_pointer" => pure (.supertraitVtablePointer)
  | other => throw s!"unrecognized vtableEntryKind tag `{other}`"

def parseVtableEntry (j : JsonReader.Slice) (path : String) : Except String VtableEntry := do
  let tag ← fieldString j "kind" path
  let traitDefinitionId ← match optionalJson j "trait_def_id" with
    | none => pure none
    | some value => pure (some (← parseDefinitionRef value (joinPath path "trait_def_id")))
  let allocationId ← match optionalJson j "allocation" with
    | none => pure none
    | some value => match isAllocationRef value with
      | some id => pure (some id)
      | none => throw s!"{joinPath path "allocation"}: expected allocation reference"
  return {
    kind := ← vtableEntryKind tag
    instanceId := ← optionalNat j "instance_id" path
    allocationId := allocationId
    traitDefinitionId := traitDefinitionId
    traitDefinitionPath := ← optionalString j "trait_def_path" path
  }

/-- Decode a source `tcx.vtable_entries` row retained outside a GlobalAlloc
image. Runtime-created vtables use this exact metadata without borrowing the
CTFE probe's allocation identity. -/
def decodeVtableEntry (j : JsonReader.Slice) (path : String := "$compiler_vtable_entry") :
    Except String VtableEntry := parseVtableEntry j path

/-- Decode compiler-query static metadata. -/
def decodeStaticGlobalInfo (j : JsonReader.Slice) (path : String := "$static_global_info") : Except String StaticGlobalInfo := do
  return {
    nested := ← fieldBool j "nested" path
    sizeBytes := ← fieldNat j "size_bytes" path
    alignBytes := ← fieldNat j "align_bytes" path
    mutability := ← match ← fieldString j "mutability" path with
      | "mutable" => pure .mutable
      | "immutable" => pure .immutable
      | tag => throw s!"{path}.mutability: unrecognized memory mutability `{tag}`"
    isStatic := ← fieldBool j "is_static" path
    foreignItem := ← fieldBool j "is_foreign_item" path
    threadLocal := ← fieldBool j "thread_local" path
  }

def parseThreadLocal (j : JsonReader.Slice) : Except String Catalog.ThreadLocal := do
  let definition ← fieldNat j "def_id" "$thread_local"
  let info ← decodeStaticGlobalInfo (← field j "global_info" "$thread_local")
  unless info.isStatic && info.threadLocal do
    throw "TLS declaration compiler query evidence is unresolved or inconsistent"
  let initializer ← field j "initializer" "$thread_local"
  let memory ← if info.foreignItem then pure none else
    some <$> parseAllocationMemory (← field initializer "allocation" "$thread_local.initializer")
      "$thread_local.initializer.allocation"
  pure { definition, info, initializer := memory }

def parseAllocation (j : JsonReader.Slice) (path : String) : Except String AllocationNode := do
  let kindText ← fieldString j "kind" path
  let kind ← allocationKind kindText
  let mut memory := none
  let mut data := none
  match kind with
  | .memory =>
    let value ← parseAllocationMemory j path
    memory := some value
    data := some (.memory value)
  | .function =>
    data := some (.function {
      instanceId := ← fieldNat j "instance_id" path

    })
  | .static =>
    let globalInfo ← match optionalField j "global_info" with
      | none => pure none
      | some info => (decodeStaticGlobalInfo info (joinPath path "global_info")).map some
    let foreignItem := globalInfo.map (·.foreignItem) |>.getD false
    let initializer ← match optionalField j "initializer" with
      | some value => (parseAllocationMemory value (joinPath path "initializer")).map some
      | none => if foreignItem then pure none else throw s!"{joinPath path "initializer"}: non-foreign static is missing its initializer image"
    data := some (.static {
      globalInfo := globalInfo
      definitionId := ← parseDefinitionRef (← field j "def_id" path) (joinPath path "def_id")
      definitionPath := ← fieldString j "def_path" path
      threadLocal := ← fieldBool j "thread_local" path
      initializer := initializer

    })
  | .vtable =>
    let predicatesJson ← arrayField j "predicates" path
    let entriesJson ← arrayField j "entries" path
    let mut predicates := #[]
    for (predicate, index) in predicatesJson.toList.zipIdx do
      predicates := predicates.push (← predicate.natural |>.mapError fun error => s!"{joinPath path "predicates"}[{index}]: expected predicate ID ({error})")
    let mut entries := #[]
    for (entry, index) in entriesJson.toList.zipIdx do
      entries := entries.push (← parseVtableEntry entry s!"{joinPath path "entries"}[{index}]")
    let typeRef ← field j "type" path
    let typeId ← match isTypeRef typeRef with
      | some id => pure id
      | none => throw s!"{joinPath path "type"}: expected type reference"
    data := some (.vtable {
      principalPredicate := ← optionalNatField j "principal_predicate" path
      typeId := typeId
      sizeBytes := ← optionalNat j "size_bytes" path
      alignBytes := ← optionalNat j "align_bytes" path
      predicates := predicates
      entries := entries

    })
  | .typeId =>
    let typeRef ← field j "type" path
    let typeId ← match isTypeRef typeRef with
      | some id => pure id
      | none => throw s!"{joinPath path "type"}: expected type reference"
    data := some (.typeId typeId)
  return {
    id := ← fieldNat j "allocation_id" path
    sourceAllocId := ← do
      match ← optionalNat j "source_alloc_id" path with
      | none => pure none
      | some value =>
        if value == 0 || value >= 2^64 then
          throw s!"{joinPath path "source_alloc_id"}: expected a nonzero u64 rustc allocation identity"
        else pure (some (UInt64.ofNat value))
    kind := kind
    memory := memory
    data := data
  }

def parseSourceAllocIdKind (value path : String) : Except String SourceAllocIdKind := do
  match value with
  | "dangling" => pure .dangling
  | "memory" => pure .memory
  | "function" => pure .function
  | "vtable" => pure .vtable
  | "static" => pure .static
  | "type_id" => pure .typeId
  | _ => throw s!"{path}: unknown source AllocId kind `{value}`"

def canonicalLowerHex (value : String) : Bool :=
  validHex value && value.toList.all (fun char =>
    (char >= '0' && char <= '9') || (char >= 'a' && char <= 'f'))

def allocationNodeMatchesSourceKind (sourceKind : SourceAllocIdKind)
    (nodeKind : AllocationKind) : Bool :=
  match sourceKind, nodeKind with
  | .memory, .memory | .function, .function | .vtable, .vtable
  | .static, .static | .typeId, .typeId => true
  | _, _ => false

def parseSourceAllocIdDedupKind (value path : String) : Except String SourceAllocIdDedupKind := do
  match value with
  | "function" => pure .function
  | "vtable" => pure .vtable
  | "static" => pure .static
  | "type_id" => pure .typeId
  | "memory" | "memory_const_allocation" => pure .memory
  | "bytes" | "byte_memory" => pure .bytes
  | _ => throw s!"{path}: unknown source AllocId dedup key kind `{value}`"

def parseSourceAllocIdPoolRow (j : JsonReader.Slice) (path : String) : Except String SourceAllocIdPoolRow := do
  let raw ← fieldNat j "source_alloc_id" path
  if raw == 0 || raw >= 2^64 then throw s!"{joinPath path "source_alloc_id"}: expected nonzero u64"
  let kind ← parseSourceAllocIdKind (← fieldString j "kind" path) (joinPath path "kind")
  let status ← match ← fieldString j "status" path with
    | "dangling" => pure SourceAllocIdStatus.dangling
    | "serialized" => pure .serialized
    | "opaque" => pure .opaque
    | value => throw s!"{joinPath path "status"}: unknown source AllocId pool status `{value}`"
  let allocationId ← optionalNatField j "allocation_id" path
  if (optionalField j "opaque_allocation_id").isSome then
    throw s!"{path}: opaque_allocation_id is not a semantic allocation witness"
  let (memoryMutability, memoryAlignBytes, memoryAllBytesInitialized, memoryHasProvenance) ←
    match kind with
    | .memory => do
      let mutability ← match ← fieldString j "memory_mutability" path with
        | "immutable" => pure MemoryMutability.immutable
        | "mutable" => pure .mutable
        | value => throw s!"{joinPath path "memory_mutability"}: unsupported value `{value}`"
      pure (some mutability,
        some (← fieldNat j "memory_align_bytes" path),
        some (← fieldBool j "memory_all_bytes_initialized" path),
        some (← fieldBool j "memory_has_provenance" path))
    | _ => pure (none,none,none,none)
  let byteImageHex ← optionalString j "byte_image_hex" path
  if let some image := byteImageHex then
    unless canonicalLowerHex image do throw s!"{joinPath path "byte_image_hex"}: expected canonical lowercase hexadecimal"
  let shapeIsValid := match kind, status, allocationId with
    | .dangling, .dangling, none => true
    | .memory, .serialized, some _ => true
    | .function, .serialized, some _ => true
    | .vtable, .serialized, some _ => true
    | .static, .serialized, some _ => true
    | .typeId, .serialized, some _ => true
    | .memory, .opaque, none => true
    | .function, .opaque, none => true
    | .vtable, .opaque, none => true
    | .static, .opaque, none => true
    | .typeId, .opaque, none => true
    | _, _, _ => false
  unless shapeIsValid do throw s!"{path}: inconsistent kind/status/allocation_id in source AllocId pool row"
  let byteEligible := kind == .memory && memoryMutability == some .immutable && memoryAlignBytes == some 1 &&
    memoryAllBytesInitialized == some true && memoryHasProvenance == some false
  match kind, byteEligible, byteImageHex with
  | .memory, true, some _ =>
    unless status == .serialized && allocationId.isSome do
      throw s!"{path}: eligible byte-memory key requires a serialized allocation node"
  | .memory, false, none => pure ()
  | .memory, _, _ => throw s!"{path}: inconsistent byte-memory eligibility and image"
  | _, _, none => pure ()
  | _, _, some _ => throw s!"{path}: byte-memory image is only valid for memory globals"
  pure ⟨UInt64.ofNat raw, kind, status, allocationId, memoryMutability, memoryAlignBytes,
    memoryAllBytesInitialized, memoryHasProvenance, byteImageHex⟩

def parseSourceAllocIdSaltResult (j : JsonReader.Slice) (path : String) : Except String SourceAllocIdSaltResult := do
  let sourceId ← fieldNat j "source_alloc_id" path
  if sourceId == 0 || sourceId >= 2^64 then throw s!"{joinPath path "source_alloc_id"}: expected nonzero u64"
  let outcome ← match ← fieldString j "probe_result" path with
    | "preexisting_hit" => pure SourceAllocIdProbeOutcome.preexistingHit
    | "miss_reserved_by_probe" => pure .missReservedByProbe
    | value => throw s!"{joinPath path "probe_result"}: unknown probe result `{value}`"
  pure {
    salt := ← fieldNat j "salt" path
    allocationId := ← fieldNat j "allocation_id" path
    sourceAllocId := UInt64.ofNat sourceId
    outcome := outcome
  }

def parseSourceAllocIdDedupRow (j : JsonReader.Slice) (path : String) : Except String SourceAllocIdDedupRow := do
  let keyKind ← parseSourceAllocIdDedupKind (← fieldString j "key_kind" path) (joinPath path "key_kind")
  let saltsJson ← arrayField j "salts" path
  let mut salts := #[]
  for (value, index) in saltsJson.toList.zipIdx do
    salts := salts.push (← parseSourceAllocIdSaltResult value s!"{path}.salts[{index}]")
  let byteImageHex ← optionalString j "bytes_hex" path
  if let some image := byteImageHex then
    unless canonicalLowerHex image do throw s!"{joinPath path "bytes_hex"}: expected canonical lowercase hexadecimal"
  let keyAllocationId ← fieldNat j "key_allocation_id" path
  match keyKind, byteImageHex with
  | .bytes, some _ => pure ()
  | .function, none => pure ()
  | .vtable, none => pure ()
  | .static, none => pure ()
  | .typeId, none => pure ()
  | .memory, none => pure ()
  | .bytes, none => throw s!"{joinPath path "bytes_hex"}: required for byte-image dedup key"
  | _, some _ => throw s!"{joinPath path "bytes_hex"}: only valid for byte-image dedup key"
  pure ⟨keyKind, keyAllocationId, byteImageHex, salts⟩

def parseCompilerAllocIdWorld (j : JsonReader.Slice) (nodes : Array AllocationNode) : Except String CompilerAllocIdWorld := do
  let path := "$.compiler_alloc_id_world"
  unless (← fieldString j "schema" path) == "rustc_alloc_id_world_v1" do
    throw "$.compiler_alloc_id_world.schema: unsupported source AllocId world schema"
  unless (← fieldString j "profile" path) == "prepared_post_export" do
    throw "$.compiler_alloc_id_world.profile: unsupported source AllocId world profile"
  let frontier ← field j "frontier" path
  let lastNat ← fieldNat frontier "last_reserved_source_alloc_id" (joinPath path "frontier")
  let nextNat ← fieldNat frontier "next_source_alloc_id" (joinPath path "frontier")
  let sentinelNat ← fieldNat frontier "final_sentinel_source_alloc_id" (joinPath path "frontier")
  if lastNat == 0 || lastNat >= 2^64 then throw "$.compiler_alloc_id_world.frontier.last_reserved_source_alloc_id: expected nonzero u64"
  if nextNat == 0 || nextNat >= 2^64 then throw "$.compiler_alloc_id_world.frontier.next_source_alloc_id: expected nonzero u64"
  if sentinelNat == 0 || sentinelNat >= 2^64 then
    throw "$.compiler_alloc_id_world.frontier.final_sentinel_source_alloc_id: expected nonzero u64"
  unless (← fieldNat j "global_pool_complete_through" path) == lastNat do
    throw "$.compiler_alloc_id_world.global_pool_complete_through: does not equal frontier"
  let pool ← (← arrayField j "raw_pool" path).mapIdxM fun index row =>
    parseSourceAllocIdPoolRow row s!"{path}.raw_pool[{index}]"
  let dedup ← (← arrayField j "dedup_catalog" path).mapIdxM fun index row =>
    parseSourceAllocIdDedupRow row s!"{path}.dedup_catalog[{index}]"
  let complete ← (← arrayField j "complete_key_families" path).mapIdxM fun index row => do
    let name ← row.string
    unless name == "byte_memory" do
      throw s!"{path}.complete_key_families[{index}]: this decoder only recognizes the source-validated byte_memory family"
    pure SourceAllocIdDedupKind.bytes
  let nonExhaustive ← (← arrayField j "non_exhaustive_key_families" path).mapIdxM fun index row => do
    parseSourceAllocIdDedupKind (← row.string) s!"{path}.non_exhaustive_key_families[{index}]"
  let world : CompilerAllocIdWorld := {
    lastReservedSourceAllocId := UInt64.ofNat lastNat
    nextSourceAllocId := UInt64.ofNat nextNat
    finalSentinelSourceAllocId := UInt64.ofNat sentinelNat
    rawPool := pool
    dedupCatalog := dedup
    completeKeyFamilies := complete
    nonExhaustiveKeyFamilies := nonExhaustive }
  validateCompilerAllocIdWorld nodes world
  pure world

def parsePromotedBodies (j : JsonReader.Slice) (path _fallbackName : String) : Except String (Array PromotedBody) := do
  let promotedJson ← match optionalJson j "promoted_bodies" with
    | none => pure #[]
    | some value => jsonArray value (joinPath path "promoted_bodies")
  let mut promotedBodies := #[]
  for (entry, index) in promotedJson.toList.zipIdx do
    let promotedPath := s!"{joinPath path "promoted_bodies"}[{index}]"
    let promotedIndex ← match optionalField entry "promoted_index" with
      | none => pure index
      | some value => value.natural |>.mapError fun e => s!"{joinPath promotedPath "promoted_index"}: expected unsigned integer ({e})"
    let body ← match optionalJson entry "body" with
      | none => pure none
      | some value => pure (some (← value.natural))
    promotedBodies := promotedBodies.push ⟨promotedIndex, body⟩
  return promotedBodies

def parseBodyRoot (j : JsonReader.Slice) (path : String) : Except String BodyRoot := do
  let defPath ← fieldString j "def_path" path
  return {
    bodyId := ← fieldNat j "body" path
    entryInstance := ← fieldNat j "entry_instance" path
    definitionId := ← fieldNat j "def_id" path
    defPath := defPath
    isStatic := ← fieldBool j "is_static" path
    threadLocalStatic := ← fieldBool j "thread_local_static" path
    promotedBodies := ← parsePromotedBodies j path defPath
  }

def parseInstance (j : JsonReader.Slice) (path : String) : Except String InstanceNode := do
  let kindText ← fieldString j "kind" path
  let kind : InstanceKind ← match kindText with
    | "instance_mir" => pure .instanceMir
    | "intrinsic_dispatch" => pure .intrinsicDispatch
    | "foreign_item_no_mir" => pure .foreignItemNoMir
    | "virtual_dispatch_target" => pure .virtualDispatchTarget
    | "identity_only" => pure .identityOnly
    | other => throw s!"{path}.kind: unrecognized instance kind `{other}`"
  let id ← fieldNat j "instance_id" path
  let defPath ← optionalString j "def_path" path
  let definitionId ← match optionalJson j "def_id" with
    | none => pure none
    | some value => pure (some (← parseDefinitionRef value (joinPath path "def_id")))
  let fallback := match defPath with
    | some value => value
    | none => s!"instance[{id}]"
  let bodyInstantiation ← match optionalJson j "body_instantiation" with
    | none => pure none
    | some value => pure (some (← parseAbiTag value (joinPath path "body_instantiation")))
  let bodyTemplateIsPolymorphic ← match optionalField j "body_template_is_polymorphic" with
    | none => pure none
    | some value => if value.isNull then pure none else (value.boolean).map some |>.mapError fun e => s!"{joinPath path "body_template_is_polymorphic"}: expected boolean ({e})"
  let instanceArgsAreMonomorphic ← match optionalField j "instance_args_are_monomorphic" with
    | none => pure none
    | some value => if value.isNull then pure none else (value.boolean).map some |>.mapError fun e => s!"{joinPath path "instance_args_are_monomorphic"}: expected boolean ({e})"
  let body ← match optionalJson j "body" with
    | none => pure none
    | some value => pure (some (← value.natural))
  let promotedBodies ← parsePromotedBodies j path fallback
  let virtualIdentity ← match optionalJson j "virtual_identity" with
    | none => pure none
    | some value => some <$> ((·, ·) <$> fieldNat value "function_type" (joinPath path "virtual_identity")
        <*> fieldNat value "fn_abi" (joinPath path "virtual_identity"))
  let foreignItem ← match optionalJson j "foreign_item" with
    | none => pure none
    | some value => some <$> value.boolean
  return {
    instanceKind := ← InstanceKindCodec.decode (← field j "instance_kind" path)
    genericArgs := ← GenericArgsCodec.decode (← field j "generic_args" path)
    id := id
    kind := kind
    defPath := defPath
    definitionId := definitionId
    bodyInstantiation := bodyInstantiation
    bodyTemplateIsPolymorphic := bodyTemplateIsPolymorphic
    instanceArgsAreMonomorphic := instanceArgsAreMonomorphic
    bodyId := body
    promotedBodies := promotedBodies
    dispatchSlot := ← optionalNat j "dispatch_slot" path
    bodyStatus := ← optionalString j "body_status" path
    virtualIdentity
    foreignItem
    symbolName := ← optionalString j "symbol_name" path
    fallbackInstance := ← optionalNat j "fallback_instance" path
  }

def passModeKind (tag : String) : Except String PassModeKind :=
  match tag with
  | "Ignore" => pure (.ignore)
  | "Direct" => pure (.direct)
  | "Pair" => pure (.pair)
  | "Cast" => pure (.cast)
  | "Indirect" => pure (.indirect)
  | "IndirectUnsized" => pure (.indirectUnsized)
  | other => throw s!"unrecognized passModeKind tag `{other}`"

def parseArgumentExtension (j : JsonReader.Slice) (path : String) : Except String ArgumentExtensionKind := do
  match ← fieldString j "kind" path with
  | "none" => pure .none
  | "zero_extend" => pure .zeroExtend
  | "sign_extend" => pure .signExtend
  | _ => throw s!"{path}: unrecognized argument extension"

def parseArgumentCapture (j : JsonReader.Slice) (path : String) : Except String ArgumentCaptureKind := do
  match ← fieldString j "kind" path with
  | "none" => pure .none
  | "address" => pure .address
  | "read_only" => pure .readOnly
  | "unrestricted" => pure .unrestricted
  | _ => throw s!"{path}: unrecognized argument capture"

def parseIndirectMode (j : JsonReader.Slice) (path : String) : Except String IndirectModeKind := do
  match ← fieldString j "kind" path with
  | "pointer" => pure .pointer
  | "on_stack" => pure .onStack
  | "amdgpu_kernel_argument" => pure .amdgpuKernelArgument
  | _ => throw s!"{path}: unrecognized indirect argument mode"

def parseAbiAttributes (j : JsonReader.Slice) (path : String) : Except String AbiAttributes := do
  return {
    noAlias := ← fieldBool j "no_alias" path
    noFree := ← fieldBool j "no_free" path
    noUndef := ← fieldBool j "no_undef" path
    nonNull := ← fieldBool j "non_null" path
    readOnly := ← fieldBool j "read_only" path
    writable := ← fieldBool j "writable" path
    inRegister := ← fieldBool j "in_register" path
    regularBits := ← fieldNat j "regular_bits" path
    pointeeSizeBytes := ← fieldNat j "pointee_size_bytes" path
    pointeeAlignBytes := ← optionalNat j "pointee_align_bytes" path
    argExtension := ← parseArgumentExtension (← field j "arg_extension" path) (joinPath path "arg_extension")
    captures := ← parseArgumentCapture (← field j "captures" path) (joinPath path "captures")
  }

def abiRegisterKind (tag : String) : Except String AbiRegisterKind :=
  match tag with
  | "integer" => pure (.integer)
  | "float" => pure (.float)
  | "ppc_f128" => pure (.ppcF128)
  | "vector" => pure (.vector)
  | other => throw s!"unrecognized abiRegisterKind tag `{other}`"

def canonicalAbiKind (tag : String) : Except String CanonicalAbiKind :=
  match tag with
  | "c" => pure (.c)
  | "rust" => pure (.rust)
  | "rust_cold" => pure (.rustCold)
  | "rust_preserve_none" => pure (.rustPreserveNone)
  | "rust_tail" => pure (.rustTail)
  | "custom" => pure (.custom)
  | "swift" => pure (.swift)
  | "arm" => pure (.arm)
  | "gpu_kernel" => pure (.gpuKernel)
  | "interrupt" => pure (.interrupt)
  | "x86" => pure (.x86)
  | other => throw s!"unrecognized canonicalAbiKind tag `{other}`"

def armCallKind (tag : String) : Except String ArmCallKind :=
  match tag with
  | "aapcs" => pure (.aapcs)
  | "cmse_nonsecure_call" => pure (.cmseNonSecureCall)
  | "cmse_nonsecure_entry" => pure (.cmseNonSecureEntry)
  | other => throw s!"unrecognized armCallKind tag `{other}`"

def interruptCallKind (tag : String) : Except String InterruptCallKind :=
  match tag with
  | "avr" => pure (.avr)
  | "avr_non_blocking" => pure (.avrNonBlocking)
  | "msp430" => pure (.msp430)
  | "riscv_machine" => pure (.riscvMachine)
  | "riscv_supervisor" => pure (.riscvSupervisor)
  | "x86" => pure (.x86)
  | other => throw s!"unrecognized interruptCallKind tag `{other}`"

def x86CallKind (tag : String) : Except String X86CallKind :=
  match tag with
  | "fastcall" => pure (.fastcall)
  | "stdcall" => pure (.stdcall)
  | "sysv64" => pure (.sysv64)
  | "thiscall" => pure (.thiscall)
  | "vectorcall" => pure (.vectorcall)
  | "win64" => pure (.win64)
  | other => throw s!"unrecognized x86CallKind tag `{other}`"

def parseCanonicalAbi (j : JsonReader.Slice) (path : String) : Except String CanonicalAbi := do
  let kindNode ← parseAbiTag j path
  return {
    kind := ← canonicalAbiKind kindNode.tag
    armCall := ← (← optionalString j "arm_call" path).mapM armCallKind
    interruptKind := ← (← optionalString j "interrupt_kind" path).mapM interruptCallKind
    x86Call := ← (← optionalString j "x86_call" path).mapM x86CallKind
  }

def parseAbiRegisterHint (j : JsonReader.Slice) (path : String) : Except String AbiRegisterHint := do
  match ← fieldString j "kind" path with
  | "integer" => return .integer (← integerTypeTag (← fieldString j "integer_kind" path)) (← fieldBool j "signed" path)
  | "float" => return .float (← floatTypeTag (← fieldString j "float_kind" path))
  | "pointer" => return .pointer (← fieldNat j "address_space" path)
  | _ => throw s!"{path}: unrecognized register primitive hint"

def parseAbiRegister (j : JsonReader.Slice) (path : String) : Except String AbiRegister := do
  let kindNode ← field j "kind" path
  let kindTag ← fieldString kindNode "kind" (joinPath path "kind")
  let hintElement ← match optionalJson kindNode "hint_element" with
    | none => pure none
    | some value => pure (some (← parseAbiRegisterHint value (joinPath path "kind.hint_element")))
  return {
    kind := ← abiRegisterKind kindTag
    sizeBits := ← fieldNat j "size_bits" path
    hintElement := hintElement
  }

def parseAbiCastTarget (j : JsonReader.Slice) (path : String) : Except String AbiCastTarget := do
  let prefixJson ← arrayField j "prefix_registers" path
  let mut prefixRegisters := #[]
  for (register, index) in prefixJson.toList.zipIdx do
    prefixRegisters := prefixRegisters.push (← parseAbiRegister register s!"{joinPath path "prefix_registers"}[{index}]")
  return {
    prefixRegisters := prefixRegisters
    restOffsetBytes := ← optionalNat j "rest_offset_bytes" path
    restRegister := ← parseAbiRegister (← field j "rest_register" path) (joinPath path "rest_register")
    restTotalBytes := ← fieldNat j "rest_total_bytes" path
    restIsConsecutive := ← fieldBool j "rest_is_consecutive" path
    attributes := ← parseAbiAttributes (← field j "attributes" path) (joinPath path "attributes")
  }

def parseAbiPassMode (j : JsonReader.Slice) (path : String) : Except String AbiPassMode := do
  let tag ← fieldString j "kind" path
  let mut attributes := #[]
  for key in ["attributes", "first", "second", "metadata_attributes"] do
    if let some attr := optionalJson j key then
      if key == "attributes" || key == "metadata_attributes" then
        attributes := attributes.push (← parseAbiAttributes attr (joinPath path key))
      else if key == "first" || key == "second" then
        attributes := attributes.push (← parseAbiAttributes attr (joinPath path key))
  let castTarget ← match optionalJson j "target" with
    | none => pure none
    | some value => pure (some (← parseAbiCastTarget value (joinPath path "target")))
  let indirectMode ← match optionalJson j "mode" with
    | none => pure none
    | some value => pure (some (← parseIndirectMode value (joinPath path "mode")))
  let padI32Count ← optionalNat j "pad_i32_count" path
  let addressSpace ← optionalNat j "address_space" path
  let kind ← passModeKind tag
  match kind with
  | .cast => if castTarget.isNone || padI32Count.isNone then throw s!"{path}: Cast pass mode is missing target/padding data"
  | .indirect => if indirectMode.isNone then throw s!"{path}: Indirect pass mode is missing its mode tag"
  | .direct | .pair | .indirectUnsized | .ignore => pure ()
  return {
    kind := kind
    attributes := attributes
    castTarget := castTarget
    padI32Count := padI32Count
    addressSpace := addressSpace
    indirectMode := indirectMode
  }

def parseAbiArgument (j : JsonReader.Slice) (path : String) : Except String AbiArgument := do
  let typeRef ← field j "type" path
  let typeId ← match isTypeRef typeRef with
    | some id => pure id
    | none => throw s!"{joinPath path "type"}: expected type reference"
  let layoutId ← fieldNat j "layout" path
  return {
    typeId := typeId
    layoutId := layoutId
    mode := ← parseAbiPassMode (← field j "mode" path) (joinPath path "mode")
  }

def parseFunctionAbi (j : JsonReader.Slice) (path : String) : Except String FunctionAbi := do
  let argsJson ← arrayField j "arguments" path
  let mut args := #[]
  let mut index := 0
  for arg in argsJson do
    args := args.push (← parseAbiArgument arg s!"{joinPath path "arguments"}[{index}]")
    index := index + 1
  let ret ← parseAbiArgument (← field j "return" path) (joinPath path "return")
  return {
    arguments := args
    returnValue := ret
    callingConvention := ← parseCanonicalAbi (← field j "calling_convention" path) (joinPath path "calling_convention")
    canUnwind := ← fieldBool j "can_unwind" path
    cVariadic := ← fieldBool j "c_variadic" path
    fixedCount := ← fieldNat j "fixed_count" path
  }

/-- Decode an exact compiler projection layout using the canonical schema. -/
def decodeCompilerLayout (j : JsonReader.Slice) : Except String Layout :=
  parseLayout j "$.compiler_projection_layout"

/-- Decode an independently keyed compiler FnAbi query using the canonical schema. -/
def decodeCompilerFunctionAbi (j : JsonReader.Slice) : Except String FunctionAbi :=
  parseFunctionAbi j "$.compiler_fn_abi"

end Miri.Input.DecoderValues

namespace Miri.Input
export DecoderValues (expectedMiriCommit expectedRustcCommit expectedSchema expectedSchemaVersion expectedCompilerAbiLayoutSchema decodeCompilerPredicateEvidence decodeCompilerPattern decodeTypeCompilerFacts decodeVtableEntry decodeStaticGlobalInfo decodeCompilerLayout decodeCompilerFunctionAbi)
end Miri.Input
