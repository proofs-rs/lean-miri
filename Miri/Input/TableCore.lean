import Miri.Input.LocalValidation
import Miri.Input.ValidateAllocIdWorld
import Miri.Input.Model.Types
import Miri.Input.Model.Catalogs
import Miri.Input.JsonReader
import Miri.Input.CompilerExternAbi
import Miri.Input.InstanceKindCodec
import Miri.Input.GenericArgsCodec

namespace Miri.Input.DecoderValues
open JsonReader

open Lean

def expectedMiriCommit : String := "7fa591d7d4dd9af8154becbc8332f8096f8323b1"
def expectedRustcCommit : String := "8144389c895da997dbdecaa635e41d6a50be6ffd"
def expectedSchema : String := "lean-miri-rustc-mir"
def expectedSchemaVersion : Nat := 13
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


def decimalNat (text path : String) : Except String Nat := do
  if text.isEmpty then throw s!"{path}: expected a nonempty unsigned decimal integer"
  let mut value := 0
  for digit in text.toList do
    if digit < '0' || digit > '9' then throw s!"{path}: expected an unsigned decimal integer"
    value := value * 10 + digit.toNat - '0'.toNat
  return value


private structure parseSourcePositionFields where
  «line» : Option (Nat) := none
  «column» : Option (Nat) := none

def parseSourcePosition (_path : String := "$parseSourcePosition") : Parser (SourcePosition) := do
  let s ← object (parseSourcePositionFields.mk none none) fun s key => do
    match key with
    | "line" => return { s with «line» := some (← natural) }
    | "column" => return { s with «column» := some (← natural) }
    | _ => skipValue; pure s
  return ⟨(← required s.«line» "line"), (← required s.«column» "column")⟩

private structure parseSourceSpanFields where
  «is_dummy» : Option (Bool) := none
  «lo» : Option (Nat) := none
  «hi» : Option (Nat) := none
  «start» : Option (SourcePosition) := none
  «end» : Option (SourcePosition) := none
  «ctxt» : Option (String) := none
  «file» : Option (Nat) := none

def parseSourceSpan (_path : String := "$parseSourceSpan") : Parser (SourceSpanData) := do
  let s ← object (parseSourceSpanFields.mk none none none none none none none) fun s key => do
    match key with
    | "is_dummy" => return { s with «is_dummy» := some (← boolean) }
    | "lo" => return { s with «lo» := some (← natural) }
    | "hi" => return { s with «hi» := some (← natural) }
    | "start" => return { s with «start» := some (← parseSourcePosition) }
    | "end" => return { s with «end» := some (← parseSourcePosition) }
    | "ctxt" => return { s with «ctxt» := some (← string) }
    | "file" => return { s with «file» := some (← natural) }
    | _ => skipValue; pure s
  return {
    isDummy := (← required s.«is_dummy» "is_dummy"), lo := (← required s.«lo» "lo"), hi := (← required s.«hi» "hi"), start := (← required s.«start» "start"),
    «end» := (← required s.«end» "end"), context := (← required s.«ctxt» "ctxt"), file := (← required s.«file» "file") }

private structure parseSourceInfoFields where
  «span» : Option (Nat) := none
  «scope» : Option (Nat) := none

def parseSourceInfo (_path : String := "$parseSourceInfo") : Parser (SourceInfo) := do
  let s ← object (parseSourceInfoFields.mk none none) fun s key => do
    match key with
    | "span" => return { s with «span» := some (← natural) }
    | "scope" => return { s with «scope» := some (← natural) }
    | _ => skipValue; pure s
  return ⟨(← required s.«span» "span"), (← required s.«scope» "scope")⟩

private structure parseTaggedFields where
  «kind» : Option (String) := none

def parseTagged (_path : String := "$parseTagged") : Parser (TaggedNode) := do
  let s ← object (parseTaggedFields.mk none) fun s key => do
    match key with
    | "kind" => return { s with «kind» := some (← string) }
    | _ => skipValue; pure s
  return ⟨(← required s.«kind» "kind")⟩

private structure abiObjectTagFields where
  «kind» : Option (String) := none
  «variant» : Option (String) := none

private def abiObjectTag  : Parser (TaggedNode) := do
  let s ← object (abiObjectTagFields.mk none none) fun s key => do
    match key with
    | "kind" => return { s with «kind» := some (← string) }
    | "variant" => return { s with «variant» := some (← string) }
    | _ => skipValue; pure s
  if s.kind.isSome && s.variant.isSome then fail "ambiguous ABI tag: both kind and variant are present"
  match s.kind.or s.variant with
  | some tag => pure ⟨tag⟩
  | none => fail "enum object is missing its kind tag"

def parseAbiTag (_path : String := "$tag") : Parser TaggedNode := do
  if (← Std.Internal.Parsec.peek!) == '"' then return ⟨← string⟩ else abiObjectTag

private structure parsePrimitiveLayoutFields where
  «kind» : Option (String) := none
  «size_bytes» : Option (Nat) := none
  «integer_kind» : Option (Option (String)) := none
  «signed» : Option (Option (Bool)) := none
  «float_kind» : Option (Option (String)) := none
  «address_space» : Option (Option (Nat)) := none

def parsePrimitiveLayout (path : String := "$parsePrimitiveLayout") : Parser (PrimitiveLayout) := do
  let s ← object (parsePrimitiveLayoutFields.mk none none none none none none) fun s key => do
    match key with
    | "kind" => return { s with «kind» := some (← string) }
    | "size_bytes" => return { s with «size_bytes» := some (← natural) }
    | "integer_kind" => return { s with «integer_kind» := some (← nullable (string)) }
    | "signed" => return { s with «signed» := some (← nullable (boolean)) }
    | "float_kind" => return { s with «float_kind» := some (← nullable (string)) }
    | "address_space" => return { s with «address_space» := some (← nullable (natural)) }
    | _ => skipValue; pure s
  let variant ← required s.«kind» "kind"
  if s.«integer_kind».isSome && !(variant == "integer") then fail s!"incompatible field `integer_kind` for variant `{variant}`"
  if s.«signed».isSome && !(variant == "integer") then fail s!"incompatible field `signed` for variant `{variant}`"
  if s.«float_kind».isSome && !(variant == "float") then fail s!"incompatible field `float_kind` for variant `{variant}`"
  if s.«address_space».isSome && !(variant == "pointer") then fail s!"incompatible field `address_space` for variant `{variant}`"
  if variant == "integer" && (s.integer_kind.join.isNone || s.signed.join.isNone) then fail "incomplete integer primitive"
  if variant == "float" && s.float_kind.join.isNone then fail "incomplete float primitive"
  if variant == "pointer" && s.address_space.join.isNone then fail "incomplete pointer primitive"
  let kind ← match (← required s.«kind» "kind") with
    | "integer" => pure PrimitiveKind.integer
    | "float" => pure .float
    | "pointer" => pure .pointer
    | other => fail s!"{path}: unrecognized PrimitiveKind `{other}`"
  let integerKind ← (s.integer_kind.join).mapM (fun value => liftExcept (integerTypeTag value))
  let floatKind ← (s.float_kind.join).mapM (fun value => liftExcept (floatTypeTag value))
  return {
    kind, sizeBytes := (← required s.«size_bytes» "size_bytes"), integerKind, floatKind,
    signed := s.signed.join, addressSpace := s.address_space.join }

def parseU128Natural (path : String := "$u128") : Parser Nat := do
  let value ← if (← Std.Internal.Parsec.peek!) == '"' then do
    let text ← string
    unless !text.isEmpty && text.toList.all Char.isDigit do fail s!"{path}: expected exact unsigned decimal string"
    let some value := text.toNat? | fail s!"{path}: invalid unsigned decimal"
    pure value
  else natural
  unless value < 2^128 do fail s!"{path}: u128 overflow"
  pure value

private structure u128RangeFields where
  «start» : Option (Nat) := none
  «end» : Option (Nat) := none

private def u128Range  : Parser (Nat × Nat) := do
  let s ← object (u128RangeFields.mk none none) fun s key => do
    match key with
    | "start" => return { s with «start» := some (← parseU128Natural) }
    | "end" => return { s with «end» := some (← parseU128Natural) }
    | _ => skipValue; pure s
  return ((← required s.«start» "start"), (← required s.«end» "end"))

private structure naturalRangeFields where
  «start» : Option (Nat) := none
  «end» : Option (Nat) := none

private def naturalRange  : Parser (Nat × Nat) := do
  let s ← object (naturalRangeFields.mk none none) fun s key => do
    match key with
    | "start" => return { s with «start» := some (← natural) }
    | "end" => return { s with «end» := some (← natural) }
    | _ => skipValue; pure s
  return ((← required s.«start» "start"), (← required s.«end» "end"))

private structure parseScalarLayoutFields where
  «kind» : Option (String) := none
  «primitive» : Option (PrimitiveLayout) := none
  «valid_range» : Option (Option (Nat × Nat)) := none

def parseScalarLayout (path : String := "$parseScalarLayout") : Parser (ScalarLayout) := do
  let s ← object (parseScalarLayoutFields.mk none none none) fun s key => do
    match key with
    | "kind" => return { s with «kind» := some (← string) }
    | "primitive" => return { s with «primitive» := some (← parsePrimitiveLayout) }
    | "valid_range" => return { s with «valid_range» := some (← nullable (u128Range)) }
    | _ => skipValue; pure s
  let variant ← required s.«kind» "kind"
  if s.«valid_range».isSome && !(variant == "initialized") then fail s!"incompatible field `valid_range` for variant `{variant}`"
  if variant == "initialized" && s.valid_range.join.isNone then fail "initialized scalar is missing valid_range"
  let kind ← match (← required s.«kind» "kind") with
    | "initialized" => pure ScalarShapeKind.initialized
    | "union" => pure .union
    | other => fail s!"{path}: unrecognized ScalarShapeKind `{other}`"
  return {
    kind, primitive := (← required s.«primitive» "primitive"), validRange := s.valid_range.join }

private structure nicheFields where
  «offset_bytes» : Option (Nat) := none
  «primitive» : Option (PrimitiveLayout) := none
  «valid_range» : Option (Nat × Nat) := none

private def niche  : Parser (NicheLayout) := do
  let s ← object (nicheFields.mk none none none) fun s key => do
    match key with
    | "offset_bytes" => return { s with «offset_bytes» := some (← natural) }
    | "primitive" => return { s with «primitive» := some (← parsePrimitiveLayout) }
    | "valid_range" => return { s with «valid_range» := some (← u128Range) }
    | _ => skipValue; pure s
  return {
    offsetBytes := (← required s.«offset_bytes» "offset_bytes"), primitive := (← required s.«primitive» "primitive"), validRange := (← required s.«valid_range» "valid_range") }

def parseNicheLayout (_path : String := "$niche") : Parser (Option NicheLayout) := nullable niche

private structure parseBackendReprFields where
  «kind» : Option (String) := none
  «scalar» : Option (Option (ScalarLayout)) := none
  «first» : Option (Option (ScalarLayout)) := none
  «second» : Option (Option (ScalarLayout)) := none
  «element» : Option (Option (ScalarLayout)) := none
  «sized» : Option (Option (Bool)) := none
  «second_offset_bytes» : Option (Option (Nat)) := none
  «lane_count» : Option (Option (Nat)) := none
  «vector_count» : Option (Option (Nat)) := none

def parseBackendRepr (path : String := "$parseBackendRepr") : Parser (BackendRepr) := do
  let s ← object (parseBackendReprFields.mk none none none none none none none none none) fun s key => do
    match key with
    | "kind" => return { s with «kind» := some (← string) }
    | "scalar" => return { s with «scalar» := some (← nullable (parseScalarLayout)) }
    | "first" => return { s with «first» := some (← nullable (parseScalarLayout)) }
    | "second" => return { s with «second» := some (← nullable (parseScalarLayout)) }
    | "element" => return { s with «element» := some (← nullable (parseScalarLayout)) }
    | "sized" => return { s with «sized» := some (← nullable (boolean)) }
    | "second_offset_bytes" => return { s with «second_offset_bytes» := some (← nullable (natural)) }
    | "lane_count" => return { s with «lane_count» := some (← nullable (natural)) }
    | "vector_count" => return { s with «vector_count» := some (← nullable (natural)) }
    | _ => skipValue; pure s
  let variant ← required s.«kind» "kind"
  if s.«scalar».isSome && !(variant == "scalar") then fail s!"incompatible field `scalar` for variant `{variant}`"
  if s.«first».isSome && !(variant == "scalar_pair") then fail s!"incompatible field `first` for variant `{variant}`"
  if s.«second».isSome && !(variant == "scalar_pair") then fail s!"incompatible field `second` for variant `{variant}`"
  if s.«second_offset_bytes».isSome && !(variant == "scalar_pair") then fail s!"incompatible field `second_offset_bytes` for variant `{variant}`"
  if s.«sized».isSome && !(variant == "memory") then fail s!"incompatible field `sized` for variant `{variant}`"
  if s.«element».isSome && !(variant == "simd_vector" || variant == "scalable_simd_vector") then fail s!"incompatible field `element` for variant `{variant}`"
  if s.«lane_count».isSome && !(variant == "simd_vector" || variant == "scalable_simd_vector") then fail s!"incompatible field `lane_count` for variant `{variant}`"
  if s.«vector_count».isSome && !(variant == "scalable_simd_vector") then fail s!"incompatible field `vector_count` for variant `{variant}`"
  if variant == "scalable_simd_vector" && s.vector_count.join.isNone then fail "scalable SIMD is missing vector_count"
  let kind ← liftExcept (backendReprKind (← required s.«kind» "kind"))
  let scalar := s.scalar.join
  let first := s.first.join
  let second := s.second.join
  let element := s.element.join
  let sized := s.sized.join
  let secondOffsetBytes := s.second_offset_bytes.join
  let laneCount := s.lane_count.join
  let vectorCount := s.vector_count.join
  match kind with
  | .scalar => if scalar.isNone then fail s!"{path}: scalar backend representation is missing scalar data"
  | .scalarPair =>
    if first.isNone || second.isNone || secondOffsetBytes.isNone then fail s!"{path}: scalar-pair backend representation is incomplete"
  | .memory => if sized.isNone then fail s!"{path}: memory backend representation is missing `sized`"
  | .simdVector | .scalableSimdVector =>
    if element.isNone || laneCount.isNone then fail s!"{path}: SIMD backend representation is incomplete"
  return {
    kind, sized, scalar, first, second, secondOffsetBytes, element, laneCount, vectorCount }

private structure parseFieldShapeFields where
  «kind» : Option (String) := none
  «field_count» : Option (Option (Nat)) := none
  «offset_bytes» : Option (Option (Nat)) := none
  «stride_bytes» : Option (Option (Nat)) := none
  «offsets_bytes» : Option (Option (Array Nat)) := none
  «memory_order» : Option (Option (Array Nat)) := none

def parseFieldShape (path : String := "$parseFieldShape") : Parser (FieldShape) := do
  let s ← object (parseFieldShapeFields.mk none none none none none none) fun s key => do
    match key with
    | "kind" => return { s with «kind» := some (← string) }
    | "field_count" => return { s with «field_count» := some (← nullable (natural)) }
    | "offset_bytes" => return { s with «offset_bytes» := some (← nullable (natural)) }
    | "stride_bytes" => return { s with «stride_bytes» := some (← nullable (natural)) }
    | "offsets_bytes" => return { s with «offsets_bytes» := some (← nullable (array natural)) }
    | "memory_order" => return { s with «memory_order» := some (← nullable (array natural)) }
    | _ => skipValue; pure s
  let variant ← required s.«kind» "kind"
  if s.«field_count».isSome && !(variant == "primitive" || variant == "union" || variant == "array" || variant == "arbitrary") then fail s!"incompatible field `field_count` for variant `{variant}`"
  if s.«offset_bytes».isSome && !(variant == "union") then fail s!"incompatible field `offset_bytes` for variant `{variant}`"
  if s.«stride_bytes».isSome && !(variant == "array") then fail s!"incompatible field `stride_bytes` for variant `{variant}`"
  if s.«offsets_bytes».isSome && !(variant == "arbitrary") then fail s!"incompatible field `offsets_bytes` for variant `{variant}`"
  if s.«memory_order».isSome && !(variant == "arbitrary") then fail s!"incompatible field `memory_order` for variant `{variant}`"
  let kind ← match (← required s.«kind» "kind") with
    | "primitive" => pure FieldShapeKind.primitive
    | "union" => pure .union
    | "array" => pure .array
    | "arbitrary" => pure .arbitrary
    | other => fail s!"{path}: unrecognized FieldShapeKind `{other}`"
  let fieldCount := s.field_count.join
  let offsetBytes := s.offset_bytes.join
  let strideBytes := s.stride_bytes.join
  let offsetsBytes := s.offsets_bytes.join.getD #[]
  let memoryOrder := s.memory_order.join.getD #[]
  match kind with
  | .primitive => pure ()
  | .union => if fieldCount.isNone || offsetBytes.isNone then fail s!"{path}: union field shape is incomplete"
  | .array => if fieldCount.isNone || strideBytes.isNone then fail s!"{path}: array field shape is incomplete"
  | .arbitrary =>
    if fieldCount.isNone || offsetsBytes.size != fieldCount.getD 0 || memoryOrder.size != fieldCount.getD 0 then
      fail s!"{path}: arbitrary field shape count/offset/order mismatch"
  return {
    kind, fieldCount := fieldCount.getD 0, offsetBytes, strideBytes, offsetsBytes, memoryOrder }

private structure parseLayoutVariantFields where
  «fields» : Option (FieldShape) := none
  «largest_niche» : Option (Option NicheLayout) := none
  «variant_index» : Option (Nat) := none
  «size_bytes» : Option (Nat) := none
  «backend_repr» : Option (BackendRepr) := none
  «field_offsets_bytes» : Option (Array (Nat)) := none
  «uninhabited» : Option (Bool) := none

def parseLayoutVariant (_path : String := "$parseLayoutVariant") : Parser (LayoutVariant) := do
  let s ← object (parseLayoutVariantFields.mk none none none none none none none) fun s key => do
    match key with
    | "fields" => return { s with «fields» := some (← parseFieldShape) }
    | "largest_niche" => return { s with «largest_niche» := some (← parseNicheLayout) }
    | "variant_index" => return { s with «variant_index» := some (← natural) }
    | "size_bytes" => return { s with «size_bytes» := some (← natural) }
    | "backend_repr" => return { s with «backend_repr» := some (← parseBackendRepr) }
    | "field_offsets_bytes" => return { s with «field_offsets_bytes» := some (← array (natural)) }
    | "uninhabited" => return { s with «uninhabited» := some (← boolean) }
    | _ => skipValue; pure s
  return {
    fields := (← required s.«fields» "fields"), largestNiche := (← required s.«largest_niche» "largest_niche"), variantIndex := (← required s.«variant_index» "variant_index"),
    sizeBytes := (← required s.«size_bytes» "size_bytes"), backendRepr := (← required s.«backend_repr» "backend_repr"), fieldOffsetsBytes := (← required s.«field_offsets_bytes» "field_offsets_bytes"),
    uninhabited := (← required s.«uninhabited» "uninhabited") }

private structure parseTagEncodingFields where
  «kind» : Option (String) := none
  «untagged_variant» : Option (Option (Nat)) := none
  «niche_variants» : Option (Option (Nat × Nat)) := none
  «niche_start» : Option (Option (String)) := none

def parseTagEncoding (path : String := "$parseTagEncoding") : Parser (TagEncoding) := do
  let s ← object (parseTagEncodingFields.mk none none none none) fun s key => do
    match key with
    | "kind" => return { s with «kind» := some (← string) }
    | "untagged_variant" => return { s with «untagged_variant» := some (← nullable (natural)) }
    | "niche_variants" => return { s with «niche_variants» := some (← nullable (naturalRange)) }
    | "niche_start" => return { s with «niche_start» := some (← nullable (string)) }
    | _ => skipValue; pure s
  let variant ← required s.«kind» "kind"
  if s.«untagged_variant».isSome && !(variant == "niche") then fail s!"incompatible field `untagged_variant` for variant `{variant}`"
  if s.«niche_variants».isSome && !(variant == "niche") then fail s!"incompatible field `niche_variants` for variant `{variant}`"
  if s.«niche_start».isSome && !(variant == "niche") then fail s!"incompatible field `niche_start` for variant `{variant}`"
  let kind ← match (← required s.«kind» "kind") with
    | "direct" => pure TagEncodingKind.direct
    | "niche" => pure .niche
    | other => fail s!"{path}: unrecognized TagEncodingKind `{other}`"
  let untaggedVariant := s.untagged_variant.join
  let nicheVariants := s.niche_variants.join
  let nicheStart ← s.niche_start.join.mapM (fun text => liftExcept (decimalNat text path))
  if kind == .niche && (untaggedVariant.isNone || nicheVariants.isNone || nicheStart.isNone) then
    fail s!"{path}: supported niche tag encoding is missing its range or start value"
  if let some (first, last) := nicheVariants then
    if last < first then fail s!"{path}.niche_variants: inclusive niche range has its end before its start"
  return ⟨kind, untaggedVariant, nicheVariants, nicheStart⟩

private structure parseVariantsLayoutFields where
  «kind» : Option (String) := none
  «variant_index» : Option (Option (Nat)) := none
  «tag» : Option (Option (ScalarLayout)) := none
  «tag_encoding» : Option (Option (TagEncoding)) := none
  «tag_field_index» : Option (Option (Nat)) := none
  «variants» : Option (Option (Array LayoutVariant)) := none

def parseVariantsLayout (path : String := "$parseVariantsLayout") : Parser (VariantsLayout) := do
  let s ← object (parseVariantsLayoutFields.mk none none none none none none) fun s key => do
    match key with
    | "kind" => return { s with «kind» := some (← string) }
    | "variant_index" => return { s with «variant_index» := some (← nullable (natural)) }
    | "tag" => return { s with «tag» := some (← nullable (parseScalarLayout)) }
    | "tag_encoding" => return { s with «tag_encoding» := some (← nullable (parseTagEncoding)) }
    | "tag_field_index" => return { s with «tag_field_index» := some (← nullable (natural)) }
    | "variants" => return { s with «variants» := some (← nullable (array parseLayoutVariant)) }
    | _ => skipValue; pure s
  let variant ← required s.«kind» "kind"
  if s.«variant_index».isSome && !(variant == "single") then fail s!"incompatible field `variant_index` for variant `{variant}`"
  if s.«tag».isSome && !(variant == "multiple") then fail s!"incompatible field `tag` for variant `{variant}`"
  if s.«tag_encoding».isSome && !(variant == "multiple") then fail s!"incompatible field `tag_encoding` for variant `{variant}`"
  if s.«tag_field_index».isSome && !(variant == "multiple") then fail s!"incompatible field `tag_field_index` for variant `{variant}`"
  if s.«variants».isSome && !(variant == "multiple") then fail s!"incompatible field `variants` for variant `{variant}`"
  let kind ← liftExcept (layoutVariantsKind (← required s.«kind» "kind"))
  let variantIndex := s.variant_index.join
  let tag := s.tag.join
  let tagEncoding := s.tag_encoding.join
  let tagFieldIndex := s.tag_field_index.join
  let variants := s.variants.join.getD #[]
  match kind with
  | .single => if variantIndex.isNone then fail s!"{path}: single-variant layout is missing variant_index"
  | .multiple =>
    if tag.isNone || tagEncoding.isNone || tagFieldIndex.isNone || variants.isEmpty then
      fail s!"{path}: multi-variant layout is missing tag or variant data"
  | .empty => pure ()
  return {
    kind, variantIndex, tag, tagEncoding, tagFieldIndex, variants }

private structure ArrayOffsetFormulaFields where
  kind : Option String := none
  stride : Option Nat := none
  count : Option Nat := none

def parseLayoutFieldOffsets : Parser LayoutFieldOffsets := do
  if (← Std.Internal.Parsec.peek!) == '[' then return .explicit (← array natural)
  let fields ← object ({} : ArrayOffsetFormulaFields) fun fields key => do
    match key with
    | "kind" => return { fields with kind := some (← string) }
    | "stride_bytes" => return { fields with stride := some (← natural) }
    | "field_count" => return { fields with count := some (← natural) }
    | _ => skipValue; pure fields
  unless (← required fields.kind "kind") == "array" do fail "unknown field offset formula kind"
  return .arrayFormula (← required fields.stride "stride_bytes") (← required fields.count "field_count")

private structure parseLayoutFields where
  primitiveRecipe : Option String := none
  «kind» : Option (String) := none
  «field_offsets_bytes» : Option LayoutFieldOffsets := none
  «fields» : Option (Option (FieldShape)) := none
  «variants» : Option (Option (VariantsLayout)) := none
  «backend_repr» : Option (Option (BackendRepr)) := none
  «size_bytes» : Option (Option (Nat)) := none
  «abi_align_bytes» : Option (Option (Nat)) := none
  «unadjusted_abi_align_bytes» : Option (Option (Nat)) := none
  «max_repr_align_bytes» : Option (Option (Nat)) := none
  «repr_c» : Option (Bool) := none
  «uninhabited» : Option (Bool) := none
  «largest_niche» : Option (Option NicheLayout) := none
  «randomization_seed» : Option (Nat) := none

def parseLayout (path : String := "$parseLayout") : Parser (Layout) := do
  let s ← object (parseLayoutFields.mk none none none none none none none none none none none none none none) fun s key => do
    match key with
    | "primitive_recipe" => return {s with primitiveRecipe := some (← string)}
    | "kind" => return { s with «kind» := some (← string) }
    | "field_offsets_bytes" => return { s with «field_offsets_bytes» := some (← parseLayoutFieldOffsets) }
    | "fields" => return { s with «fields» := some (← nullable (parseFieldShape)) }
    | "variants" => return { s with «variants» := some (← nullable (parseVariantsLayout)) }
    | "backend_repr" => return { s with «backend_repr» := some (← nullable (parseBackendRepr)) }
    | "size_bytes" => return { s with «size_bytes» := some (← nullable (natural)) }
    | "abi_align_bytes" => return { s with «abi_align_bytes» := some (← nullable (natural)) }
    | "unadjusted_abi_align_bytes" => return { s with «unadjusted_abi_align_bytes» := some (← nullable (natural)) }
    | "max_repr_align_bytes" => return { s with «max_repr_align_bytes» := some (← nullable (natural)) }
    | "repr_c" => return { s with «repr_c» := some (← boolean) }
    | "uninhabited" => return { s with «uninhabited» := some (← boolean) }
    | "largest_niche" => return { s with «largest_niche» := some (← parseNicheLayout) }
    | "randomization_seed" => return { s with «randomization_seed» := some (← natural) }
    | _ => skipValue; pure s
  if let some recipe := s.primitiveRecipe then
    unless s.kind.isNone && s.field_offsets_bytes.isNone && s.fields.isNone &&
        s.variants.isNone && s.backend_repr.isNone && s.size_bytes.isNone &&
        s.abi_align_bytes.isNone && s.unadjusted_abi_align_bytes.isNone &&
        s.max_repr_align_bytes.isNone && s.repr_c.isNone && s.uninhabited.isNone &&
        s.largest_niche.isNone && s.randomization_seed.isNone do
      fail s!"{path}: primitive recipe cannot contain eager layout results"
    unless ["bool", "char", "i8", "i16", "i32", "i64", "i128", "isize",
        "u8", "u16", "u32", "u64", "u128", "usize", "f16", "f32", "f64", "f128",
        "fn_pointer", "never"].contains recipe do
      fail s!"{path}: unknown primitive layout recipe"
    return {
      primitiveRecipe := some recipe, kind := .layout,
      maxReprAlignBytes := none, reprC := false, uninhabited := false,
      largestNiche := none, randomizationSeed := 0, sizeBytes := none,
      abiAlignBytes := none, unadjustedAbiAlignBytes := none,
      fieldOffsetsBytes := .explicit #[], fields := none, variantsLayout := none,
      backendRepresentation := none, variantsKind := none, backendReprKind := none,
      variants := none, backendRepr := none }
  unless s.kind.isNone || s.kind == some "layout" do fail s!"{path}: unrecognized LayoutKind"
  let offsets := (← required s.«field_offsets_bytes» "field_offsets_bytes")
  let fields := s.fields.join
  let variantsLayout := s.variants.join
  let backendRepresentation := s.backend_repr.join
  let sizeBytes := s.size_bytes.join
  let abiAlignBytes := s.abi_align_bytes.join
  let unadjustedAbiAlignBytes := s.unadjusted_abi_align_bytes.join
  if sizeBytes.isNone || abiAlignBytes.isNone || unadjustedAbiAlignBytes.isNone then
    fail s!"{path}: supported layout is missing size/alignment fields"
  if fields.isNone || variantsLayout.isNone || backendRepresentation.isNone then
    fail s!"{path}: supported layout is missing field/variant/backend representation data"
  if let some shape := fields then
    liftExcept (offsets.validate shape)
  let variantsKind := variantsLayout.map (·.kind)
  let variants : Option TaggedNode := variantsKind.map fun k => ⟨match k with
    | .single => "single" | .multiple => "multiple" | .empty => "empty"⟩
  let backendReprKind := backendRepresentation.map (·.kind)
  let backend : Option TaggedNode := backendReprKind.map fun k => ⟨match k with
    | .scalar => "scalar" | .scalarPair => "scalar_pair" | .memory => "memory"
    | .simdVector => "simd_vector" | .scalableSimdVector => "scalable_simd_vector"⟩
  return {
    kind := .layout, sizeBytes, abiAlignBytes, unadjustedAbiAlignBytes,
    maxReprAlignBytes := (← required s.«max_repr_align_bytes» "max_repr_align_bytes"), reprC := (← required s.«repr_c» "repr_c"), uninhabited := (← required s.«uninhabited» "uninhabited"),
    largestNiche := (← required s.«largest_niche» "largest_niche"), randomizationSeed := (← required s.«randomization_seed» "randomization_seed"),
    fieldOffsetsBytes := offsets, fields, variantsLayout, backendRepresentation, variantsKind,
    backendReprKind, variants, backendRepr := backend }

private structure parseFunctionSignatureFields where
  «inputs» : Option (Array (Nat)) := none
  «output» : Option (Nat) := none
  «safety» : Option (TaggedNode) := none
  «abi» : Option (Miri.ABI.ExternAbi) := none
  «c_variadic» : Option (Bool) := none

def parseFunctionSignature (path : String := "$parseFunctionSignature") : Parser (FunctionSignature) := do
  let s ← object (parseFunctionSignatureFields.mk none none none none none) fun s key => do
    match key with
    | "inputs" => return { s with «inputs» := some (← array (natural)) }
    | "output" => return { s with «output» := some (← natural) }
    | "safety" => return { s with «safety» := some (← parseAbiTag) }
    | "abi" => return { s with «abi» := some (← CompilerExternAbi.decode) }
    | "c_variadic" => return { s with «c_variadic» := some (← boolean) }
    | _ => skipValue; pure s
  let safety ← match (← required s.«safety» "safety").tag with
    | "safe" => pure Miri.MIR.Safety.Safe
    | "unsafe" => pure .Unsafe
    | _ => fail s!"{path}: unknown function signature safety"
  return {
    inputs := (← required s.«inputs» "inputs"), output := (← required s.«output» "output"), safety, abi := (← required s.«abi» "abi"), cVariadic := (← required s.«c_variadic» "c_variadic") }

private structure decodeCompilerPredicateEvidenceFields where
  «predicate_id» : Option (Nat) := none
  «typing_env» : Option (String) := none
  «stable_key» : Option (Nat) := none
  «auto_trait» : Option (Bool) := none
  «normalization» : Option (Option (Nat)) := none
  «original» : Option (Nat) := none

def decodeCompilerPredicateEvidence  : Parser (CompilerPredicateEvidence) := do
  let s ← object (decodeCompilerPredicateEvidenceFields.mk none none none none none none) fun s key => do
    match key with
    | "predicate_id" => return { s with «predicate_id» := some (← natural) }
    | "typing_env" => return { s with «typing_env» := some (← string) }
    | "stable_key" => return { s with «stable_key» := some (← natural) }
    | "auto_trait" => return { s with «auto_trait» := some (← boolean) }
    | "normalization" => return { s with «normalization» := some (← nullable (natural)) }
    | "original" => return { s with «original» := some (← natural) }
    | _ => skipValue; pure s
  return {
    id := (← required s.«predicate_id» "predicate_id"), typingEnvironment := (← required s.«typing_env» "typing_env"), stableKey := (← required s.«stable_key» "stable_key"),
    autoTrait := (← required s.«auto_trait» "auto_trait"), normalizedId := (← required s.«normalization» "normalization"), original := (← required s.«original» "original") }

private structure decodeCompilerPatternFields where
  «kind» : Option (String) := none
  «start» : Option (Nat) := none
  «end» : Option (Nat) := none
  «patterns» : Option (Array (CompilerPattern)) := none

partial def decodeCompilerPattern  : Parser (CompilerPattern) := do
  let s ← object (decodeCompilerPatternFields.mk none none none none) fun s key => do
    match key with
    | "kind" => return { s with «kind» := some (← string) }
    | "start" => return { s with «start» := some (← natural) }
    | "end" => return { s with «end» := some (← natural) }
    | "patterns" => return { s with «patterns» := some (← array (decodeCompilerPattern)) }
    | _ => skipValue; pure s
  let variant ← required s.«kind» "kind"
  if s.«start».isSome && !(variant == "range") then fail s!"incompatible field `start` for variant `{variant}`"
  if s.«end».isSome && !(variant == "range") then fail s!"incompatible field `end` for variant `{variant}`"
  if s.«patterns».isSome && !(variant == "or") then fail s!"incompatible field `patterns` for variant `{variant}`"
  match (← required s.«kind» "kind") with
  | "range" => return .range (← required s.«start» "start") (← required s.«end» "end")
  | "or" => return .or (← required s.«patterns» "patterns")
  | "not_null" => pure .notNull
  | _ => fail "unknown compiler PatternKind"

private structure projectionFieldFields where
  «index» : Option (Nat) := none
  «type» : Option (Nat) := none
  «layout» : Option (Nat) := none

private def projectionField  : Parser (ProjectionField) := do
  let s ← object (projectionFieldFields.mk none none none) fun s key => do
    match key with
    | "index" => return { s with «index» := some (← natural) }
    | "type" => return { s with «type» := some (← natural) }
    | "layout" => return { s with «layout» := some (← natural) }
    | _ => skipValue; pure s
  return {
    index := (← required s.«index» "index"), typeId := (← required s.«type» "type"), layoutId := (← required s.«layout» "layout") }

private structure projectionParentFields where
  «variant» : Option (Option (Nat)) := none
  «layout» : Option (Nat) := none
  «fields» : Option (Array (ProjectionField)) := none

private def projectionParent  : Parser (ProjectionParent) := do
  let s ← object (projectionParentFields.mk none none none) fun s key => do
    match key with
    | "variant" => return { s with «variant» := some (← nullable (natural)) }
    | "layout" => return { s with «layout» := some (← natural) }
    | "fields" => return { s with «fields» := some (← array (projectionField)) }
    | _ => skipValue; pure s
  return {
    variant := s.variant.join, layoutId := (← required s.«layout» "layout"), fields := (← required s.«fields» "fields") }

private structure parseProjectionQueriesFields where
  «typing_env» : Option (String) := none
  «parents» : Option (Array (ProjectionParent)) := none

private def parseProjectionQueries (_path : String := "$parseProjectionQueries") : Parser (ProjectionQueries) := do
  let s ← object (parseProjectionQueriesFields.mk none none) fun s key => do
    match key with
    | "typing_env" => return { s with «typing_env» := some (← string) }
    | "parents" => return { s with «parents» := some (← array (projectionParent)) }
    | _ => skipValue; pure s
  return {
    typingEnvironment := (← required s.«typing_env» "typing_env"), parents := (← required s.«parents» "parents") }

private structure discriminantFields where
  «variant» : Option (Nat) := none
  «bits» : Option (String) := none
  «type» : Option (Nat) := none

private def discriminant  : Parser (DiscriminantValue) := do
  let s ← object (discriminantFields.mk none none none) fun s key => do
    match key with
    | "variant" => return { s with «variant» := some (← natural) }
    | "bits" => return { s with «bits» := some (← string) }
    | "type" => return { s with «type» := some (← natural) }
    | _ => skipValue; pure s
  let variant := (← required s.«variant» "variant")
  unless variant < 2^32 do fail "compiler variant index exceeds u32"
  let bits ← liftExcept (decimalNat (← required s.«bits» "bits") "$discriminant")
  unless bits < 2^128 do fail "compiler discriminant exceeds u128"
  return {
    variant, typeId := (← required s.«type» "type"), bits }

private structure parseDiscriminantsFields where
  «has_discriminants» : Option (Bool) := none
  «adt_variant_count» : Option (Option (Nat)) := none
  «values» : Option (Array (DiscriminantValue)) := none

def parseDiscriminants (_path : String := "$parseDiscriminants") : Parser (DiscriminantInfo) := do
  let s ← object (parseDiscriminantsFields.mk none none none) fun s key => do
    match key with
    | "has_discriminants" => return { s with «has_discriminants» := some (← boolean) }
    | "adt_variant_count" => return { s with «adt_variant_count» := some (← nullable (natural)) }
    | "values" => return { s with «values» := some (← array (discriminant)) }
    | _ => skipValue; pure s
  return {
    hasDiscriminants := (← required s.«has_discriminants» "has_discriminants"), adtVariantCount := s.adt_variant_count.join, values := (← required s.«values» "values") }

private structure adtFactsFields where
  «definition» : Option (Nat) := none
  «item_name» : Option (String) := none
  «nonnull_optimization_guaranteed» : Option (Bool) := none

private def adtFacts  : Parser (AdtCompilerFacts) := do
  let s ← object (adtFactsFields.mk none none none) fun s key => do
    match key with
    | "definition" => return { s with «definition» := some (← natural) }
    | "item_name" => return { s with «item_name» := some (← string) }
    | "nonnull_optimization_guaranteed" => return { s with «nonnull_optimization_guaranteed» := some (← boolean) }
    | _ => skipValue; pure s
  return {
    definitionId := (← required s.«definition» "definition"), itemName := (← required s.«item_name» "item_name"), nonnullOptimizationGuaranteed := (← required s.«nonnull_optimization_guaranteed» "nonnull_optimization_guaranteed") }

private structure simdShapeFields where
  «count» : Option (Nat) := none
  «element» : Option (Nat) := none

private def simdShape  : Parser (Nat × TypeId) := do
  let s ← object (simdShapeFields.mk none none) fun s key => do
    match key with
    | "count" => return { s with «count» := some (← natural) }
    | "element" => return { s with «element» := some (← natural) }
    | _ => skipValue; pure s
  let count := (← required s.«count» "count")
  unless count < 2^64 do fail "SIMD lane count exceeds u64"
  return (count, (← required s.«element» "element"))

def booleanQueries : Parser (Array (String × Bool)) :=
  object #[] fun out key => do return out.push (key, ← boolean)

private def typeQueries : Parser (Array (String × Option Nat)) :=
  object #[] fun out key => do return out.push (key, ← nullable natural)

private structure decodeTypeCompilerFactsFields where
  «typing_env» : Option (String) := none
  «boolean_queries» : Option (Array (String × Bool)) := none
  «type_queries» : Option (Array (String × Option Nat)) := none
  «capture_names» : Option (Option (Array (Option String))) := none
  «adt» : Option (Option (AdtCompilerFacts)) := none
  «projection_queries» : Option (Option (ProjectionQueries)) := none
  «simd_size_and_type» : Option (Option (Nat × TypeId)) := none
  «discriminants» : Option (Option (DiscriminantInfo)) := none
  «type_id_hash» : Option (String) := none
  «definition» : Option (Option (Nat)) := none

def decodeTypeCompilerFacts (path : String := "$decodeTypeCompilerFacts")
    (booleanPool : Array (Array (String × Bool)) := #[])
    (discriminantPool : Array DiscriminantInfo := #[]) : Parser TypeCompilerFacts := do
  let s ← object (decodeTypeCompilerFactsFields.mk none none none none none none none none none none) fun s key => do
    match key with
    | "typing_env" => return { s with «typing_env» := some (← string) }
    | "boolean_queries" =>
      let id ← natural
      let some value := booleanPool[id]? | fail s!"{path}.boolean_queries: out of bounds shared boolean query set {id}"
      return { s with «boolean_queries» := some value }
    | "type_queries" => return { s with «type_queries» := some (← typeQueries) }
    | "capture_names" => return { s with «capture_names» := some (← nullable (array (nullable string))) }
    | "adt" => return { s with «adt» := some (← nullable (adtFacts)) }
    | "projection_queries" => return { s with «projection_queries» := some (← nullable (parseProjectionQueries)) }
    | "simd_size_and_type" => return { s with «simd_size_and_type» := some (← nullable (simdShape)) }
    | "discriminants" =>
      let id ← nullable natural
      let value ← id.mapM fun id => do
        let some value := discriminantPool[id]? | fail s!"{path}.discriminants: out of bounds shared discriminants {id}"
        pure value
      return { s with «discriminants» := some value }
    | "type_id_hash" => return { s with «type_id_hash» := some (← string) }
    | "definition" => return { s with «definition» := some (← nullable (natural)) }
    | _ => skipValue; pure s
  let typeIdHash ← s.type_id_hash.mapM fun text => do
    let bits ← liftExcept (decimalNat text path)
    unless bits < 2^128 do fail s!"{path}: compiler TypeId hash exceeds u128"
    pure bits
  return {
    typingEnvironment := (← required s.«typing_env» "typing_env"), booleanQueries := (← required s.«boolean_queries» "boolean_queries"), typeQueries := (← required s.«type_queries» "type_queries"),
    captureNames := s.capture_names.join, adt := (← required s.«adt» "adt"), projectionQueries := (← required s.«projection_queries» "projection_queries"),
    simdSizeAndType := (← required s.«simd_size_and_type» "simd_size_and_type"), discriminants := (← required s.«discriminants» "discriminants"),
    typeIdHash, definitionId := s.definition.join }

private structure reprIntegerFields where
  «kind» : Option (String) := none
  «signed» : Option (Bool) := none
  «integer_kind» : Option (String) := none
  «size_bits» : Option (Nat) := none

private def reprInteger  : Parser (ReprInteger) := do
  let s ← object (reprIntegerFields.mk none none none none) fun s key => do
    match key with
    | "kind" => return { s with «kind» := some (← string) }
    | "signed" => return { s with «signed» := some (← boolean) }
    | "integer_kind" => return { s with «integer_kind» := some (← string) }
    | "size_bits" => return { s with «size_bits» := some (← natural) }
    | _ => skipValue; pure s
  let variant ← required s.«kind» "kind"
  if s.«integer_kind».isSome && !(variant == "fixed") then fail s!"incompatible field `integer_kind` for variant `{variant}`"
  if s.«size_bits».isSome && !(variant == "fixed") then fail s!"incompatible field `size_bits` for variant `{variant}`"
  match (← required s.«kind» "kind") with
  | "pointer_sized" => return .pointerSized (← required s.«signed» "signed")
  | "fixed" => return .fixed (← liftExcept (integerTypeTag (← required s.«integer_kind» "integer_kind"))) (← required s.«size_bits» "size_bits") (← required s.«signed» "signed")
  | _ => fail "unknown representation integer"

private structure scalableElementFields where
  «kind» : Option (String) := none
  «count» : Option (Nat) := none

private def scalableElement  : Parser (ScalableElement) := do
  let s ← object (scalableElementFields.mk none none) fun s key => do
    match key with
    | "kind" => return { s with «kind» := some (← string) }
    | "count" => return { s with «count» := some (← natural) }
    | _ => skipValue; pure s
  let variant ← required s.«kind» "kind"
  if s.«count».isSome && !(variant == "element_count") then fail s!"incompatible field `count` for variant `{variant}`"
  match (← required s.«kind» "kind") with
  | "element_count" => return .elementCount (← required s.«count» "count")
  | "container" => pure .container
  | _ => fail "unknown scalable representation"

private structure parseReprOptionsFields where
  «integer» : Option (Option (ReprInteger)) := none
  «align_bytes» : Option (Option (Nat)) := none
  «pack_bytes» : Option (Option (Nat)) := none
  «scalable_element» : Option (Option (ScalableElement)) := none
  «flags_bits» : Option (Nat) := none
  «field_shuffle_seed» : Option (Nat) := none

private def parseReprOptions (_path : String := "$parseReprOptions") : Parser (ReprOptions) := do
  let s ← object (parseReprOptionsFields.mk none none none none none none) fun s key => do
    match key with
    | "integer" => return { s with «integer» := some (← nullable (reprInteger)) }
    | "align_bytes" => return { s with «align_bytes» := some (← nullable (natural)) }
    | "pack_bytes" => return { s with «pack_bytes» := some (← nullable (natural)) }
    | "scalable_element" => return { s with «scalable_element» := some (← nullable (scalableElement)) }
    | "flags_bits" => return { s with «flags_bits» := some (← natural) }
    | "field_shuffle_seed" => return { s with «field_shuffle_seed» := some (← natural) }
    | _ => skipValue; pure s
  return {
    integer := (← required s.«integer» "integer"), alignBytes := (← required s.«align_bytes» "align_bytes"), packBytes := (← required s.«pack_bytes» "pack_bytes"),
    scalableElement := (← required s.«scalable_element» "scalable_element"),
    flagsBits := (← required s.«flags_bits» "flags_bits"), fieldShuffleSeed := (← required s.«field_shuffle_seed» "field_shuffle_seed") }

private structure adtFieldFields where
  «index» : Option (Nat) := none
  «name» : Option (String) := none
  «type» : Option (Nat) := none

private def adtField  : Parser (AdtField) := do
  let s ← object (adtFieldFields.mk none none none) fun s key => do
    match key with
    | "index" => return { s with «index» := some (← natural) }
    | "name" => return { s with «name» := some (← string) }
    | "type" => return { s with «type» := some (← natural) }
    | _ => skipValue; pure s
  return ⟨(← required s.«index» "index"), (← required s.«name» "name"), (← required s.«type» "type")⟩

private structure adtVariantFields where
  «index» : Option (Nat) := none
  «name» : Option (String) := none
  «fields» : Option (Array (AdtField)) := none

private def adtVariant  : Parser (AdtVariant) := do
  let s ← object (adtVariantFields.mk none none none) fun s key => do
    match key with
    | "index" => return { s with «index» := some (← natural) }
    | "name" => return { s with «name» := some (← string) }
    | "fields" => return { s with «fields» := some (← array (adtField)) }
    | _ => skipValue; pure s
  let fields := (← required s.«fields» "fields")
  for i in [:fields.size] do
    unless (fields[i]?).map (·.index) == some i do fail "ADT field/index mismatch"
  return ⟨(← required s.«index» "index"), (← required s.«name» "name"), fields⟩

private structure parseShapeMutabilityFields where
  «kind» : Option (String) := none

private def parseShapeMutability (path : String := "$parseShapeMutability") : Parser (Miri.MIR.Mutability) := do
  let s ← object (parseShapeMutabilityFields.mk none) fun s key => do
    match key with
    | "kind" => return { s with «kind» := some (← string) }
    | _ => skipValue; pure s
  match (← required s.«kind» "kind") with
  | "mutable" => pure .Mut
  | "immutable" => pure .Not
  | _ => fail s!"{path}: unknown mutability"

private structure arrayIdentityFields where
  «count» : Option (Nat) := none
  «canonical_value_constructor» : Option (Bool) := none

private def arrayIdentity  : Parser (ArrayConstructor) := do
  let s ← object (arrayIdentityFields.mk none none) fun s key => do
    match key with
    | "count" => return { s with «count» := some (← natural) }
    | "canonical_value_constructor" => return { s with «canonical_value_constructor» := some (← boolean) }
    | _ => skipValue; pure s
  return ⟨(← required s.«count» "count"), (← required s.«canonical_value_constructor» "canonical_value_constructor")⟩

private structure aliasPayloadFields where
  «def_id» : Option (Nat) := none
  «kind» : Option (String) := none

private def aliasPayload  : Parser (Nat × AliasTypeKind) := do
  let s ← object (aliasPayloadFields.mk none none) fun s key => do
    match key with
    | "def_id" => return { s with «def_id» := some (← natural) }
    | "kind" => return { s with «kind» := some (← string) }
    | _ => skipValue; pure s
  let kind ← match (← required s.«kind» "kind") with
    | "Projection" => pure AliasTypeKind.projection
    | "Inherent" => pure .inherent
    | "Opaque" => pure .opaque
    | "Free" => pure .free
    | _ => fail "unknown alias kind"
  return ((← required s.«def_id» "def_id"), kind)

private structure parseTypeShapeFields where
  «kind» : Option (String) := none
  «signed_kind» : Option (String) := none
  «unsigned_kind» : Option (String) := none
  «float_kind» : Option (String) := none
  «def_id» : Option (Nat) := none
  «generic_args» : Option (Array Miri.MIR.GenericArg) := none
  «signature» : Option (FunctionSignature) := none
  «signature_bound_variables» : Option (Array (Miri.MIR.BoundVariableKind)) := none
  «region» : Option (Miri.MIR.Region) := none
  «mutability» : Option (Miri.MIR.Mutability) := none
  «element» : Option (Nat) := none
  «length» : Option (Nat) := none
  «constructor_identity» : Option (ArrayConstructor) := none
  «base» : Option (Nat) := none
  «pattern» : Option (CompilerPattern) := none
  «pointee» : Option (Nat) := none
  «inner» : Option (Nat) := none
  «bound_variables» : Option (Array (Miri.MIR.BoundVariableKind)) := none
  «predicates» : Option (Array (Nat)) := none
  «principal_predicate» : Option (Option (Nat)) := none
  «upvar_count» : Option (Nat) := none
  «elements» : Option (Array (Nat)) := none
  «alias_payload» : Option (Nat × AliasTypeKind) := none
  «adt_kind» : Option (String) := none
  «representation» : Option (ReprOptions) := none
  «variants» : Option (Array (AdtVariant)) := none

private def parseTypeShape (path : String := "$parseTypeShape") : Parser (TypeShape) := do
  let s ← object (parseTypeShapeFields.mk none none none none none none none none none none none none none none none none none none none none none none none none none none) fun s key => do
    match key with
    | "kind" => return { s with «kind» := some (← string) }
    | "signed_kind" => return { s with «signed_kind» := some (← string) }
    | "unsigned_kind" => return { s with «unsigned_kind» := some (← string) }
    | "float_kind" => return { s with «float_kind» := some (← string) }
    | "def_id" => return { s with «def_id» := some (← natural) }
    | "generic_args" => return { s with «generic_args» := some (← GenericArgsCodec.decode) }
    | "signature" => return { s with «signature» := some (← parseFunctionSignature) }
    | "signature_bound_variables" => return { s with «signature_bound_variables» := some (← array (GenericArgsCodec.boundVariable)) }
    | "region" => return { s with «region» := some (← GenericArgsCodec.region) }
    | "mutability" => return { s with «mutability» := some (← parseShapeMutability) }
    | "element" => return { s with «element» := some (← natural) }
    | "length" => return { s with «length» := some (← natural) }
    | "constructor_identity" => return { s with «constructor_identity» := some (← arrayIdentity) }
    | "base" => return { s with «base» := some (← natural) }
    | "pattern" => return { s with «pattern» := some (← decodeCompilerPattern) }
    | "pointee" => return { s with «pointee» := some (← natural) }
    | "inner" => return { s with «inner» := some (← natural) }
    | "bound_variables" => return { s with «bound_variables» := some (← array (GenericArgsCodec.boundVariable)) }
    | "predicates" => return { s with «predicates» := some (← array (natural)) }
    | "principal_predicate" => return { s with «principal_predicate» := some (← nullable (natural)) }
    | "upvar_count" => return { s with «upvar_count» := some (← natural) }
    | "elements" => return { s with «elements» := some (← array (natural)) }
    | "alias_payload" => return { s with «alias_payload» := some (← aliasPayload) }
    | "adt_kind" => return { s with «adt_kind» := some (← string) }
    | "representation" => return { s with «representation» := some (← parseReprOptions) }
    | "variants" => return { s with «variants» := some (← array (adtVariant)) }
    | _ => skipValue; pure s
  let variant ← required s.«kind» "kind"
  if s.«signed_kind».isSome && !(variant == "int") then fail s!"incompatible field `signed_kind` for variant `{variant}`"
  if s.«unsigned_kind».isSome && !(variant == "uint") then fail s!"incompatible field `unsigned_kind` for variant `{variant}`"
  if s.«float_kind».isSome && !(variant == "float") then fail s!"incompatible field `float_kind` for variant `{variant}`"
  if s.«def_id».isSome && !(variant == "adt" || variant == "foreign" || variant == "function_definition" || variant == "closure" || variant == "coroutine_closure" || variant == "coroutine" || variant == "alias") then fail s!"incompatible field `def_id` for variant `{variant}`"
  if s.«generic_args».isSome && !(variant == "adt" || variant == "function_definition" || variant == "closure" || variant == "coroutine_closure" || variant == "coroutine" || variant == "alias") then fail s!"incompatible field `generic_args` for variant `{variant}`"
  if s.«signature».isSome && !(variant == "function_definition" || variant == "function_pointer") then fail s!"incompatible field `signature` for variant `{variant}`"
  if s.«signature_bound_variables».isSome && !(variant == "function_definition" || variant == "function_pointer") then fail s!"incompatible field `signature_bound_variables` for variant `{variant}`"
  if s.«region».isSome && !(variant == "reference" || variant == "dynamic_trait_object") then fail s!"incompatible field `region` for variant `{variant}`"
  if s.«mutability».isSome && !(variant == "reference" || variant == "raw_pointer") then fail s!"incompatible field `mutability` for variant `{variant}`"
  if s.«element».isSome && !(variant == "array" || variant == "slice") then fail s!"incompatible field `element` for variant `{variant}`"
  if s.«length».isSome && !(variant == "array") then fail s!"incompatible field `length` for variant `{variant}`"
  if s.«constructor_identity».isSome && !(variant == "array") then fail s!"incompatible field `constructor_identity` for variant `{variant}`"
  if s.«base».isSome && !(variant == "pattern_type") then fail s!"incompatible field `base` for variant `{variant}`"
  if s.«pattern».isSome && !(variant == "pattern_type") then fail s!"incompatible field `pattern` for variant `{variant}`"
  if s.«pointee».isSome && !(variant == "raw_pointer" || variant == "reference") then fail s!"incompatible field `pointee` for variant `{variant}`"
  if s.«inner».isSome && !(variant == "unsafe_binder") then fail s!"incompatible field `inner` for variant `{variant}`"
  if s.«bound_variables».isSome && !(variant == "unsafe_binder") then fail s!"incompatible field `bound_variables` for variant `{variant}`"
  if s.«predicates».isSome && !(variant == "dynamic_trait_object") then fail s!"incompatible field `predicates` for variant `{variant}`"
  if s.«principal_predicate».isSome && !(variant == "dynamic_trait_object") then fail s!"incompatible field `principal_predicate` for variant `{variant}`"
  if s.«upvar_count».isSome && !(variant == "closure") then fail s!"incompatible field `upvar_count` for variant `{variant}`"
  if s.«elements».isSome && !(variant == "tuple") then fail s!"incompatible field `elements` for variant `{variant}`"
  if s.«alias_payload».isSome && !(variant == "alias") then fail s!"incompatible field `alias_payload` for variant `{variant}`"
  if s.«adt_kind».isSome && !(variant == "adt") then fail s!"incompatible field `adt_kind` for variant `{variant}`"
  if s.«representation».isSome && !(variant == "adt") then fail s!"incompatible field `representation` for variant `{variant}`"
  if s.«variants».isSome && !(variant == "adt") then fail s!"incompatible field `variants` for variant `{variant}`"
  match (← required s.«kind» "kind") with
  | "bool" => pure .bool
  | "char" => pure .char
  | "int" =>
    let spelling := (← required s.«signed_kind» "signed_kind")
    unless ["i8", "i16", "i32", "i64", "i128", "isize"].contains spelling do fail s!"{path}: expected signed integer kind"
    return .int (← liftExcept (integerTypeTag spelling))
  | "uint" =>
    let spelling := (← required s.«unsigned_kind» "unsigned_kind")
    unless ["u8", "u16", "u32", "u64", "u128", "usize"].contains spelling do fail s!"{path}: expected unsigned integer kind"
    return .uint (← liftExcept (integerTypeTag spelling))
  | "float" => return .float (← liftExcept (floatTypeTag (← required s.«float_kind» "float_kind")))
  | "adt" =>
    let variants := (← required s.«variants» "variants")
    for i in [:variants.size] do
      unless (variants[i]?).map (·.index) == some i do fail s!"{path}: ADT variant/index mismatch"
    return .adt {
      definition := (← required s.«def_id» "def_id"), kind := ← liftExcept (adtKindTag (← required s.«adt_kind» "adt_kind")),
      representation := (← required s.«representation» "representation"), args := (← required s.«generic_args» "generic_args"), variants }
  | "foreign" => return .foreign (← required s.«def_id» "def_id")
  | "str" => pure .str
  | "array" => return .array (← required s.«element» "element") (← required s.«length» "length") (← required s.«constructor_identity» "constructor_identity")
  | "pattern_type" => return .patternType (← required s.«base» "base") (← required s.«pattern» "pattern")
  | "slice" => return .slice (← required s.«element» "element")
  | "raw_pointer" => return .rawPointer (← required s.«pointee» "pointee") (← required s.«mutability» "mutability")
  | "reference" => return .reference (← required s.«pointee» "pointee") (← required s.«mutability» "mutability") (← required s.«region» "region")
  | "function_definition" => return .functionDefinition (← required s.«def_id» "def_id") (← required s.«generic_args» "generic_args") (← required s.«signature» "signature") (← required s.«signature_bound_variables» "signature_bound_variables")
  | "function_pointer" => return .functionPointer (← required s.«signature» "signature") (← required s.«signature_bound_variables» "signature_bound_variables")
  | "unsafe_binder" => return .unsafeBinder (← required s.«inner» "inner") (← required s.«bound_variables» "bound_variables")
  | "dynamic_trait_object" => return .dynamicTraitObject (← required s.«predicates» "predicates") (← required s.«principal_predicate» "principal_predicate") (← required s.«region» "region")
  | "closure" => return .closure (← required s.«def_id» "def_id") (← required s.«generic_args» "generic_args") (← required s.«upvar_count» "upvar_count")
  | "coroutine_closure" => return .coroutineClosure (← required s.«def_id» "def_id") (← required s.«generic_args» "generic_args")
  | "coroutine" => return .coroutine (← required s.«def_id» "def_id") (← required s.«generic_args» "generic_args")
  | "never" => pure .never
  | "tuple" => return .tuple (← required s.«elements» "elements")
  | "alias" =>
    let payload := (← required s.«alias_payload» "alias_payload")
    let definition := (← required s.«def_id» "def_id")
    unless payload.1 == definition do fail s!"{path}: alias definition mismatch"
    return .alias payload.2 definition (← required s.«generic_args» "generic_args")
  | tag => fail s!"{path}: unrecognized type shape `{tag}`"

private structure parseTypeNodeFields where
  «layout_query_input_type» : Option (Option (Nat)) := none
  «compiler_facts» : Option (TypeCompilerFacts) := none
  «type_id» : Option (Nat) := none
  «display» : Option (String) := none
  «shape» : Option (TypeShape) := none
  «layout» : Option (Nat) := none

def parseTypeNode (path : String := "$parseTypeNode")
    (booleanPool : Array (Array (String × Bool)) := #[])
    (discriminantPool : Array DiscriminantInfo := #[]) : Parser TypeNode := do
  let s ← object (parseTypeNodeFields.mk none none none none none none) fun s key => do
    match key with
    | "layout_query_input_type" => return { s with «layout_query_input_type» := some (← nullable (natural)) }
    | "compiler_facts" => return { s with «compiler_facts» := some (← decodeTypeCompilerFacts (path ++ ".compiler_facts") booleanPool discriminantPool) }
    | "type_id" => return { s with «type_id» := some (← natural) }
    | "display" => return { s with «display» := some (← string) }
    | "shape" => return { s with «shape» := some (← parseTypeShape) }
    | "layout" => return { s with «layout» := some (← natural) }
    | _ => skipValue; pure s
  let node : TypeNode := {
    layoutQueryInputTypeId := (← required s.«layout_query_input_type» "layout_query_input_type"), compilerFacts := s.compiler_facts,
    id := (← required s.«type_id» "type_id"), display := (← required s.«display» "display"), shape := (← required s.«shape» "shape"), layoutId := (← required s.«layout» "layout") }
  liftExcept (LocalValidation.validateType node)
  pure node

end Miri.Input.DecoderValues
