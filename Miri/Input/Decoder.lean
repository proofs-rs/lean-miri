import Miri.Input.Model
import Miri.Input.SharedPayloads
import Miri.Input.JsonTraversalCache

namespace Miri.Input

open Lean

def expectedMiriCommit : String := "7fa591d7d4dd9af8154becbc8332f8096f8323b1"
def expectedRustcCommit : String := "8144389c895da997dbdecaa635e41d6a50be6ffd"
def expectedSchema : String := "lean-miri-rustc-mir"
def expectedSchemaVersion : Nat := 3
def expectedCompilerAbiLayoutSchema : String := "physical_ty_and_layout_v1"

private def escapePathKey (key : String) : String :=
  key.toList.foldl (fun out char => out ++ match char with
    | '%' => "%25"
    | '\\' => "%5C"
    | '.' => "%2E"
    | '[' => "%5B"
    | ']' => "%5D"
    | _ => String.ofList [char]) ""

private def joinPath (path key : String) : String :=
  let key := escapePathKey key
  if path.isEmpty then key else path ++ "." ++ key

private def field (j : Json) (key path : String) : Except String Json := do
  j.getObjVal? key |>.mapError fun e => s!"{path}: missing/invalid field `{key}` ({e})"

private def fieldNat (j : Json) (key path : String) : Except String Nat := do
  let v ← field j key path
  v.getNat? |>.mapError fun e => s!"{joinPath path key}: expected unsigned integer ({e})"

private def fieldString (j : Json) (key path : String) : Except String String := do
  let v ← field j key path
  v.getStr? |>.mapError fun e => s!"{joinPath path key}: expected string ({e})"

private def fieldBool (j : Json) (key path : String) : Except String Bool := do
  let v ← field j key path
  v.getBool? |>.mapError fun e => s!"{joinPath path key}: expected boolean ({e})"

private def arrayField (j : Json) (key path : String) : Except String (Array Json) := do
  let v ← field j key path
  v.getArr? |>.mapError fun e => s!"{joinPath path key}: expected array ({e})"

private def optionalNatField (j : Json) (key path : String) : Except String (Option Nat) := do
  let v ← field j key path
  if v == .null then pure none else
    (v.getNat?).map some |>.mapError fun e => s!"{joinPath path key}: expected unsigned integer or null ({e})"

private def optionalField (j : Json) (key : String) : Option Json :=
  (j.getObjVal? key).toOption

private def optionalString (j : Json) (key path : String) : Except String (Option String) := do
  match optionalField j key with
  | none | some .null => pure none
  | some value => (value.getStr?).map some |>.mapError fun e => s!"{joinPath path key}: expected string ({e})"

private def objectFields (j : Json) : Except String (Array (String × Json)) := do
  match j with
  | .obj fields => pure fields.toList.toArray
  | _ => throw "expected object"

private def statusOf? (j : Json) : Option String :=
  match optionalField j "status" with
  | none => none
  | some value => match value.getStr? with | .ok text => some text | .error _ => none

private def parseStatus (value : String) : PayloadStatus :=
  match value with
  | "supported" | "complete" => .supported
  | "unsupported" => .unsupported
  | "unknown" => .unknown
  | "incomplete" => .incomplete
  | "debug_payload" => .debugPayload
  | other => .unrecognized other

private def sourceDebugString (j : Json) (key path : String) : Except String String := do
  let value ← field j key path
  match value with
  | .str text => pure text
  | .obj _ =>
    if statusOf? value != some "debug_payload" then
      throw s!"{joinPath path key}: expected string or diagnostic debug payload"
    fieldString value "rustc_debug" (joinPath path key)
  | _ => throw s!"{joinPath path key}: expected string or diagnostic debug payload"

/-- Parsed successful shared payloads are memoized per input document. Keys use
the canonical JSON encoding so inline copies and DAG references share entries;
failed parses are never cached, preserving diagnostics at each occurrence. -/
private structure DecodeMemo where
  sourceSpans : Std.HashMap Json SourceSpanData := {}
  layouts : Std.HashMap Json Layout := {}

private def parseSourcePosition (j : Json) (path : String) : Except String SourcePosition := do
  return {
    line := ← fieldNat j "line" path
    column := ← fieldNat j "column" path
  }

private def parseSourceSpanUncached (j : Json) (path : String) : Except String SourceSpanData := do
  if (j.getObjVal? "$lean_miri_shared_ref").isOk then
    throw s!"{path}: shared span reference requires a shared_payloads catalog"
  let start ← parseSourcePosition (← field j "start" path) (joinPath path "start")
  let endPos ← parseSourcePosition (← field j "end" path) (joinPath path "end")
  return {
    originalPayload := j.compress
    lo := ← fieldNat j "lo" path
    hi := ← fieldNat j "hi" path
    start := start
    «end» := endPos
    context := ← sourceDebugString j "ctxt" path
    file := ← sourceDebugString j "file" path
  }

private def parseSourceSpan (j : Json) (path : String) (memo : DecodeMemo := {}) : Except String SourceSpanData := do
  match memo.sourceSpans[j]? with
  | some value => pure value
  | none => parseSourceSpanUncached j path

private def parseSourceInfo (j : Json) (path : String) (memo : DecodeMemo := {}) : Except String SourceInfo := do
  return {
    span := ← parseSourceSpan (← field j "span" path) (joinPath path "span") memo
    scope := ← fieldNat j "scope" path
  }

private def hasField (j : Json) (key : String) : Bool := (j.getObjVal? key).isOk

private def isSourceSpanJson (j : Json) : Bool :=
  hasField j "lo" && hasField j "hi" && hasField j "start" && hasField j "end" &&
    hasField j "ctxt" && hasField j "file"

private def statementVariant (tag : String) : StatementVariant :=
  match tag with
  | "Assign" => .assign
  | "FakeRead" => .fakeRead
  | "SetDiscriminant" => .setDiscriminant
  | "StorageLive" => .storageLive
  | "StorageDead" => .storageDead
  | "PlaceMention" => .placeMention
  | "AscribeUserType" => .ascribeUserType
  | "Coverage" => .coverage
  | "Intrinsic" => .intrinsic
  | "ConstEvalCounter" => .constEvalCounter
  | "Nop" => .nop
  | "BackwardIncompatibleDropHint" => .backwardIncompatibleDropHint
  | other => .unknown other

private def terminatorVariant (tag : String) : TerminatorVariant :=
  match tag with
  | "Goto" => .goto
  | "SwitchInt" => .switchInt
  | "UnwindResume" => .unwindResume
  | "UnwindTerminate" => .unwindTerminate
  | "Return" => .return
  | "Unreachable" => .unreachable
  | "Drop" => .drop
  | "Call" => .call
  | "TailCall" => .tailCall
  | "Assert" => .assert
  | "Yield" => .yield
  | "CoroutineDrop" => .coroutineDrop
  | "FalseEdge" => .falseEdge
  | "FalseUnwind" => .falseUnwind
  | "InlineAsm" => .inlineAsm
  | other => .unknown other

private def rvalueVariant (tag : String) : RvalueVariant :=
  match tag with
  | "Use" => .use
  | "Repeat" => .repeat
  | "Ref" => .ref
  | "ThreadLocalRef" => .threadLocalRef
  | "RawPtr" => .rawPtr
  | "Cast" => .cast
  | "BinaryOp" => .binaryOp
  | "UnaryOp" => .unaryOp
  | "Discriminant" => .discriminant
  | "Aggregate" => .aggregate
  | "CopyForDeref" => .copyForDeref
  | "WrapUnsafeBinder" => .wrapUnsafeBinder
  | "Reborrow" => .reborrow
  | other => .unknown other

private def operandVariant (tag : String) : OperandVariant :=
  match tag with
  | "Copy" => .copy
  | "Move" => .move
  | "Constant" => .constant
  | "RuntimeChecks" => .runtimeChecks
  | other => .unknown other

private def projectionVariant (tag : String) : ProjectionVariant :=
  match tag with
  | "Deref" => .deref
  | "Field" => .field
  | "Index" => .index
  | "ConstantIndex" => .constantIndex
  | "Subslice" => .subslice
  | "Downcast" => .downcast
  | "OpaqueCast" => .opaqueCast
  | "UnwrapUnsafeBinder" => .unwrapUnsafeBinder
  | "PhantomDeref" => .phantomDeref
  | other => .unknown other

private def typeShapeKind (tag : String) : TypeShapeKind :=
  match tag with
  | "bool" => .bool
  | "char" => .char
  | "int" => .int
  | "uint" => .uint
  | "float" => .float
  | "adt" => .adt
  | "foreign" => .foreign
  | "str" => .str
  | "array" => .array
  | "pattern_type" => .patternType
  | "slice" => .slice
  | "raw_pointer" => .rawPointer
  | "reference" => .reference
  | "function_definition" => .functionDefinition
  | "function_pointer" => .functionPointer
  | "unsafe_binder" => .unsafeBinder
  | "dynamic_trait_object" => .dynamicTraitObject
  | "closure" => .closure
  | "coroutine_closure" => .coroutineClosure
  | "coroutine" => .coroutine
  | "coroutine_witness" => .coroutineWitness
  | "never" => .never
  | "tuple" => .tuple
  | "alias" => .alias
  | "parameter" => .parameter
  | "bound_type" => .boundType
  | "placeholder_type" => .placeholderType
  | "inference_type" => .inferenceType
  | "error_type" => .errorType
  | other => .unknown other

private inductive Domain where
  | any | statement | terminator | rvalue | operand | projection
  | statementWrapper | terminatorWrapper
  deriving BEq, Hashable

private structure DecodeValueKey where
  json : Json
  domain : Domain
  tagCategory : Option TypedEnumTag
  isRegionPath : Bool
  isHirIdPath : Bool
  isCoveragePath : Bool
  isCastCoercionPath : Bool
  deriving BEq, Hashable

private def decodeValueKey (j : Json) (path : String) (domain : Domain)
    (tagCategory : Option TypedEnumTag) : DecodeValueKey := {
  json := j
  domain := domain
  tagCategory := tagCategory
  isRegionPath := path.endsWith ".region"
  isHirIdPath := path.endsWith ".hir_id"
  isCoveragePath := path.endsWith ".coverage"
  isCastCoercionPath := path.endsWith ".cast_kind.coercion"
}

private def asTag? (j : Json) (key : String) : Option String :=
  match optionalField j key with
  | none => none
  | some value => match value.getStr? with | .ok text => some text | .error _ => none

private def singletonRef (j : Json) (key : String) : Option Nat :=
  match objectFields j with
  | .error _ => none
  | .ok fields =>
    match fields.toList with
    | [(name, value)] =>
      if name != key then none else
        match value.getNat? with | .ok id => some id | .error _ => none
    | _ => none

private def isTypeRef (j : Json) : Option Nat := singletonRef j "type_id"

private def isAllocationRef (j : Json) : Option Nat := do
  singletonRef j "allocation_id"

private def childDomain (parent : Domain) (key : String) : Domain :=
  match parent, key with
  | .statementWrapper, "kind" => .statement
  | .terminatorWrapper, "kind" => .terminator
  | _, "rvalue" => .rvalue
  | _, "operand" | _, "function" | _, "condition" | _, "discriminant" => .operand
  | _, "projection" => .projection
  | _, "statements" => .statementWrapper
  | _, "terminator" => .terminatorWrapper
  | _, _ => .any

private def isKnownStatement (tag : String) : Bool :=
  match statementVariant tag with | .unknown _ => false | _ => true
private def isKnownTerminator (tag : String) : Bool :=
  match terminatorVariant tag with | .unknown _ => false | _ => true
private def isKnownRvalue (tag : String) : Bool :=
  match rvalueVariant tag with | .unknown _ => false | _ => true
private def isKnownOperand (tag : String) : Bool :=
  match operandVariant tag with | .unknown _ => false | _ => true
private def isKnownProjection (tag : String) : Bool :=
  match projectionVariant tag with | .unknown _ => false | _ => true

private def recognizedAutoDomain (j : Json) : Option Domain :=
  if (optionalField j "status").isSome then
  if let some v := asTag? j "variant" then
    if isKnownStatement v then some .statement
    else if isKnownTerminator v then some .terminator
    else none
  else
    match asTag? j "kind" with
    | none => none
    | some tag =>
      if isKnownRvalue tag then some .rvalue
      else if isKnownOperand tag then some .operand
      else if isKnownProjection tag then some .projection
      else none
  else none

private def domainTag (j : Json) (domain : Domain) : Option String :=
  match domain with
  | .statement | .terminator | .statementWrapper | .terminatorWrapper => asTag? j "variant"
  | .rvalue | .operand | .projection => asTag? j "kind"
  | .any => none

private def isStringJson (j : Json) : Bool :=
  match j with | .str _ => true | _ => false

private def integerTypeTag (text : String) : IntegerTypeTag :=
  match text with
  | "i8" => .known .i8 | "i16" => .known .i16 | "i32" => .known .i32
  | "i64" => .known .i64 | "i128" => .known .i128 | "isize" => .known .isize
  | "u8" => .known .u8 | "u16" => .known .u16 | "u32" => .known .u32
  | "u64" => .known .u64 | "u128" => .known .u128 | "usize" => .known .usize
  | other => .unknown other

private def floatTypeTag (text : String) : FloatTypeTag :=
  match text with
  | "f16" => .f16 | "f16b" => .f16b | "f32" => .f32 | "f64" => .f64
  | "f128" => .f128 | "ppcf128" => .ppcf128
  | other => .unknown other

private def adtKindTag (text : String) : AdtKind :=
  match text with
  | "struct" => .structKind
  | "union" => .unionKind
  | "enum" => .enumKind
  | other => .unknown other

private def binOpFromExportTag (tag : String) : Option Miri.MIR.BinOp :=
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

private def unOpFromExportTag (tag : String) : Option Miri.MIR.UnOp :=
  match tag with
  | "not" => some .Not
  | "negate" => some .Neg
  | "pointer_metadata" => some .PtrMetadata
  | _ => Miri.MIR.UnOp.ofString tag

private def statusField (j : Json) (path : String) (optional : Bool := false)
    : Except String PayloadStatus := do
  match optionalField j "status" with
  | none =>
    if optional then pure .supported
    else throw s!"{joinPath path "status"}: missing required status tag"
  | some value =>
    let text ← value.getStr? |>.mapError fun e => s!"{joinPath path "status"}: expected string ({e})"
    pure (parseStatus text)

private def parseOperatorTag (j : Json) (path : String) : Except String (String × PayloadStatus) := do
  match j with
  | .str tag => pure (tag, .supported)
  | .obj _ =>
    let tag ← fieldString j "kind" path
    let status ← statusField j path
    pure (tag, status)
  | _ => throw s!"{path}: expected tagged operator object"

private def typedEnumCategory? (key path : String) (parentTag : Option String) (j : Json) : Option TypedEnumTag := Id.run do
  let hasKind := (optionalField j "kind").isSome
  let hasStatus := (optionalField j "status").isSome
  match key with
  | "safety" => if hasKind || isStringJson j then some .safety else none
  | "borrow_kind" => if hasKind then some .borrowKind else none
  | "fake_kind" => if isStringJson j then some .fakeBorrowKind else none
  | "mutability_kind" => if isStringJson j then some .mutBorrowKind else none
  | "mutability" => if hasKind then some .mutability else none
  | "cast_kind" => if hasKind then some .castKind else none
  | "coercion" => if hasKind then some .pointerCoercion else none
  | "source" =>
    if path.endsWith ".cast_kind.coercion" && hasKind then some .coercionSource else none
  | "aggregate_kind" => if hasKind then some .aggregateKind else none
  | "unwind" => if hasKind then some .unwindAction else none
  | "phase" | "injection_phase" =>
    if hasKind && hasStatus then some .mirPhase
    else if isStringJson j then some .mirPhaseStage
    else none
  | "retag" => if hasKind && hasStatus then some .withRetag else none
  | "check" => if parentTag == some "RuntimeChecks" && hasKind && hasStatus then some .runtimeCheck else none
  | "cause" => if hasKind && hasStatus then some .fakeReadCause else none
  | "call_source" => if hasKind && hasStatus then some .callSource else none
  | "reason" =>
    if parentTag == some "BackwardIncompatibleDropHint" && hasKind && hasStatus then
      some .backwardDropReason
    else if hasKind && hasStatus then some .unwindReason
    else none
  | "region" => if hasKind && hasStatus then some .regionKind else none
  | "bound_kind" => if hasKind && hasStatus then some .boundRegionKind else none
  | "index_kind" => if hasKind then some .boundVarIndexKind else none
  | "parameter" => if path.endsWith ".region" && hasKind then some .lateParamRegionKind else none
  | "signed_kind" | "unsigned_kind" | "integer_kind" => if isStringJson j then some .integerType else none
  | "float_kind" => if isStringJson j then some .floatType else none
  | "adt_kind" => if isStringJson j then some .adtKind else none
  | "variance" => if hasKind && hasStatus then some .variance else none
  | "coverage" => if parentTag == some "Coverage" && hasKind && hasStatus then some .coverageKind else none
  | "point_kind" => if path.endsWith ".coverage" && isStringJson j then some .coveragePointKind else none
  | "retag_mode" => if isStringJson j then some .fakeBorrowRetagMode else none
  | _ => none

private def parseInlineTag (j : Json) (path : String) : Except String TaggedNode := do
  match j with
  | .str tag => return ⟨.supported, tag, j⟩
  | .obj _ =>
    let tag ← fieldString j "kind" path
    let status ← match optionalField j "status" with
      | none => pure .supported
      | some value => parseStatus <$> (value.getStr? |>.mapError fun e => s!"{joinPath path "status"}: expected string ({e})")
    return ⟨status, tag, j⟩
  | _ => throw s!"{path}: expected enum tag object or string"

private def userTypeProjectionKind (j : Json) (path : String) : Except String UserTypeProjectionKind := do
  let tag ← fieldString j "kind" path
  match tag with
  | "Deref" => pure .deref
  | "Field" => pure (.field (← fieldNat j "index" path))
  | "Index" => pure .index
  | "ConstantIndex" =>
    pure (.constantIndex (← fieldNat j "offset" path) (← fieldNat j "min_length" path)
      (← fieldBool j "from_end" path))
  | "Subslice" =>
    pure (.subslice (← fieldNat j "from" path) (← fieldNat j "to" path)
      (← fieldBool j "from_end" path))
  | "Downcast" =>
    let nameValue ← field j "name" path
    let name ← match nameValue with
      | .null => pure none
      | _ => (nameValue.getStr?).map some |>.mapError fun e => s!"{joinPath path "name"}: expected string or null ({e})"
    pure (.downcast name (← fieldNat j "variant_index" path))
  | "OpaqueCast" => pure .opaqueCast
  | "UnwrapUnsafeBinder" => pure .unwrapUnsafeBinder
  | "PhantomDeref" => pure .phantomDeref
  | other => pure (.unknown other)

private def parseUserTypeProjection (j : Json) (path : String) : Except String UserTypeProjection := do
  let status ← statusField j path
  let baseIndex ← match optionalField j "base_index" with
    | none | some .null => pure none
    | some value => (value.getNat?).map some |>.mapError fun e => s!"{joinPath path "base_index"}: expected unsigned integer ({e})"
  let projections ← match optionalField j "projections" with
    | none | some .null => pure none
    | some _ =>
      let json ← arrayField j "projections" path
      let mut parsed := #[]
      for (item, index) in json.toList.zipIdx do
        parsed := parsed.push (← userTypeProjectionKind item s!"{joinPath path "projections"}[{index}]")
      pure (some parsed)
  if status == .supported && (baseIndex.isNone || projections.isNone) then
    throw s!"{path}: supported user-type projection is missing base index or projection sequence"
  return ⟨status, baseIndex, projections, j⟩

private abbrev DecodeValueM := StateT (Std.HashMap DecodeValueKey TypedValue) (Except String)

mutual
private partial def decodeValueM (j : Json) (path : String) (domain : Domain)
    (tagCategory : Option TypedEnumTag) (memo : DecodeMemo) : DecodeValueM TypedValue := do
  let key := decodeValueKey j path domain tagCategory
  if let some value := (← get).get? key then return value
  let value ← decodeValueBody j path domain tagCategory memo
  modify fun cache => cache.insert key value
  return value

private partial def decodeValueBody (j : Json) (path : String) (domain : Domain)
    (tagCategory : Option TypedEnumTag) (memo : DecodeMemo) : DecodeValueM TypedValue := do
  if let some id := isTypeRef j then return .typeRef id
  if let some id := isAllocationRef j then return .allocationRef id
  if statusOf? j == some "debug_payload" then return .diagnostic j
  match j with
  | .arr values =>
    let mut decoded := #[]
    let mut index := 0
    for value in values do
      decoded := decoded.push (← decodeValueM value s!"{path}[{index}]" domain tagCategory memo)
      index := index + 1
    return .array decoded
  | .obj _ =>
    if isSourceSpanJson j then return .sourceSpan (← parseSourceSpan j path memo)
    if hasField j "span" && hasField j "scope" then
      return .sourceInfo (← parseSourceInfo j path memo)
    let effectiveDomain := if domain == .any then
      match recognizedAutoDomain j with | some detected => detected | none => .any
      else domain
    let fields ← objectFields j
    let mut decodedFields := #[]
    let parentTag := match effectiveDomain with
      | .rvalue | .operand | .statement | .terminator => domainTag j effectiveDomain
      | _ => none
    for (key, value) in fields do
      let nextDomain := childDomain effectiveDomain key
      let decoded ← if key == "user_type_projection" && parentTag == some "AscribeUserType" then
          .userTypeProjection <$> parseUserTypeProjection value (joinPath path key)
        else if key == "operator" && (parentTag == some "BinaryOp" || optionalField j "kind" == some (.str "Overflow")) then
          let (tag, status) ← parseOperatorTag value (joinPath path key)
          match binOpFromExportTag tag with
          | some op => pure (.binOperator op status)
          | none => pure (.unknownBinOperator tag status)
        else if key == "operator" && parentTag == some "UnaryOp" then
          let (tag, status) ← parseOperatorTag value (joinPath path key)
          match unOpFromExportTag tag with
          | some op => pure (.unOperator op status)
          | none => pure (.unknownUnOperator tag status)
        else decodeValueM value (joinPath path key) nextDomain (typedEnumCategory? key path parentTag value) memo
      let isTagField := match effectiveDomain with
        | .statement | .terminator | .rvalue | .operand | .projection => key == "status" || key == "variant" || key == "kind"
        | _ => false
      let decoded := match key, value with
        | "instance_id", .num _ =>
          match value.getNat? with | .ok id => .instanceRef id | .error _ => decoded
        | "local", .num _ =>
          match value.getNat? with | .ok id => .localRef id | .error _ => decoded
        | "block", .num _ | "target", .num _ | "otherwise", .num _
        | "real_target", .num _ | "imaginary_target", .num _ | "resume", .num _ =>
          match value.getNat? with | .ok id => .blockRef id | .error _ => decoded
        | _, _ => decoded
      if !isTagField then decodedFields := decodedFields.push (key, decoded)
    match effectiveDomain with
    | .statement =>
      let tag ← fieldString j "variant" path
      let status := parseStatus (← fieldString j "status" path)
      return .statement (statementVariant tag) status decodedFields
    | .terminator =>
      let tag ← fieldString j "variant" path
      let status := parseStatus (← fieldString j "status" path)
      return .terminator (terminatorVariant tag) status decodedFields
    | .rvalue =>
      let tag ← fieldString j "kind" path
      let status := parseStatus (← fieldString j "status" path)
      if tag == "BinaryOp" || tag == "UnaryOp" then
        let operator ← field j "operator" path
        let _ ← parseOperatorTag operator (joinPath path "operator")
      return .rvalue (rvalueVariant tag) status decodedFields
    | .operand =>
      let tag ← fieldString j "kind" path
      let status := parseStatus (← fieldString j "status" path)
      return .operand (operandVariant tag) status decodedFields
    | .projection =>
      let tag ← fieldString j "kind" path
      return .projection (projectionVariant tag) decodedFields
    | .any | .statementWrapper | .terminatorWrapper =>
      match tagCategory with
      | some category => return .enumTag category (← parseInlineTag j path) decodedFields
      | none => return .object decodedFields
  | .str _ =>
    match tagCategory with
    | some category => return .enumTag category (← parseInlineTag j path) #[]
    | none => return .scalar j
  | _ => return .scalar j
end

private def decodeValue (j : Json) (path : String) (domain : Domain := .any)
    (tagCategory : Option TypedEnumTag := none) (memo : DecodeMemo := {}) : Except String TypedValue := do
  (decodeValueM j path domain tagCategory memo).run' {}

private def statusObligation? (status : PayloadStatus) (path : String) : Option Obligation :=
  match status with
  | .supported | .debugPayload => none
  | .unsupported => some ⟨path, "exporter marked this payload unsupported; it is an unresolved semantic obligation"⟩
  | .unknown => some ⟨path, "exporter could not resolve this payload; it is an unresolved obligation"⟩
  | .incomplete => some ⟨path, "exporter marked this payload incomplete; it is an unresolved obligation"⟩
  | .unrecognized value => some ⟨path, s!"unrecognized status `{value}`"⟩

private def unknownTagObligation (tag : String) (path : String) : Obligation :=
  ⟨path, s!"unrecognized pinned MIR enum tag `{tag}`; update decoder and review its semantics"⟩

private def enumTagKnown (category : TypedEnumTag) (tag : String) : Bool :=
  match category with
  | .safety => tag == "safe" || tag == "unsafe"
  | .borrowKind => tag == "shared" || tag == "mutable" || tag == "fake"
  | .fakeBorrowKind => tag == "shallow" || tag == "deep"
  | .mutBorrowKind => tag == "default" || tag == "two_phase" || tag == "closure_capture"
  | .mutability => tag == "mutable" || tag == "immutable"
  | .castKind => tag == "PointerExposeProvenance" || tag == "PointerWithExposedProvenance" ||
      tag == "PointerCoercion" || tag == "IntToInt" || tag == "FloatToInt" ||
      tag == "FloatToFloat" || tag == "IntToFloat" || tag == "PtrToPtr" ||
      tag == "FnPtrToPtr" || tag == "Transmute" || tag == "BoxDerefTransmute" || tag == "Subtype"
  | .pointerCoercion => tag == "ReifyFnPointer" || tag == "UnsafeFnPointer" ||
      tag == "ClosureFnPointer" || tag == "MutToConstPointer" || tag == "ArrayToPointer" || tag == "Unsize"
  | .coercionSource => tag == "as_cast" || tag == "implicit"
  | .unwindReason => tag == "abi" || tag == "in_cleanup"
  | .aggregateKind => tag == "Array" || tag == "Tuple" || tag == "Adt" ||
      tag == "Closure" || tag == "Coroutine" || tag == "CoroutineClosure" || tag == "RawPtr"
  | .unwindAction => tag == "Continue" || tag == "Unreachable" || tag == "Terminate" || tag == "Cleanup"
  | .mirPhase => tag == "built" || tag == "analysis" || tag == "runtime"
  | .mirPhaseStage => tag == "initial" || tag == "post_cleanup" || tag == "optimized"
  | .withRetag => tag == "yes" || tag == "no"
  | .runtimeCheck => tag == "ub_checks" || tag == "contract_checks" || tag == "overflow_checks"
  | .fakeReadCause => tag == "match_guard" || tag == "matched_place" ||
      tag == "guard_binding" || tag == "let_binding" || tag == "index"
  | .callSource => tag == "overloaded_operator" || tag == "match_comparison" ||
      tag == "miscellaneous_desugaring" || tag == "clone_or_use" || tag == "normal_call"
  | .backwardDropReason => tag == "edition_2024"
  | .regionKind => tag == "early_parameter" || tag == "bound" || tag == "late_parameter" ||
      tag == "static" || tag == "inference_variable" || tag == "placeholder" ||
      tag == "erased" || tag == "error"
  | .boundRegionKind => tag == "anonymous" || tag == "named_for_printing" ||
      tag == "named" || tag == "closure_environment"
  | .boundVarIndexKind => tag == "bound" || tag == "canonical"
  | .lateParamRegionKind => tag == "anonymous" || tag == "named_anonymous" ||
      tag == "named" || tag == "closure_environment"
  | .integerType => ["i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32", "u64", "u128", "usize"].contains tag
  | .floatType => ["f16", "f16b", "f32", "f64", "f128", "ppcf128"].contains tag
  | .adtKind => tag == "struct" || tag == "union" || tag == "enum"
  | .variance => tag == "covariant" || tag == "contravariant" || tag == "invariant" || tag == "bivariant"
  | .coverageKind => tag == "point" || tag == "block_marker" || tag == "virtual_counter"
  | .coveragePointKind => tag == "expr" || tag == "implicit_else" || tag == "function_end"
  | .fakeBorrowRetagMode => tag == "default"
  | .other _ => false

private def valueLocalObligationsInto (value : TypedValue) (path : String)
    (initial : Array Obligation) : Array Obligation := Id.run do
  match value with
  | .scalar _ | .diagnostic _ | .typeRef _ | .allocationRef _ | .instanceRef _
  | .localRef _ | .blockRef _ | .sourceSpan _ | .sourceInfo _ => return initial
  | .binOperator _ status | .unOperator _ status =>
      return match statusObligation? status path with
        | some issue => initial.push issue
        | none => initial
  | .unknownBinOperator tag status | .unknownUnOperator tag status =>
      let withTag := initial.push (unknownTagObligation tag path)
      return match statusObligation? status path with
        | some issue => withTag.push issue
        | none => withTag
  | .enumTag category tag children => do
      let mut out := initial
      if let some issue := statusObligation? tag.status path then out := out.push issue
      if !enumTagKnown category tag.tag then
        out := out.push (unknownTagObligation tag.tag (joinPath path "kind"))
      if category == .mirPhase then
        let phaseValue := children.find? fun (key, _) => key == "phase"
        match tag.tag with
        | "built" =>
          if phaseValue.isSome then out := out.push ⟨path, "built MIR phase must not include a subphase"⟩
        | "analysis" | "runtime" =>
          match phaseValue with
          | none => out := out.push ⟨joinPath path "phase", "analysis/runtime MIR phase is missing its subphase"⟩
          | some (_, .enumTag .mirPhaseStage phaseTag _) =>
            let valid := if tag.tag == "analysis" then
              phaseTag.tag == "initial" || phaseTag.tag == "post_cleanup"
              else phaseTag.tag == "initial" || phaseTag.tag == "post_cleanup" || phaseTag.tag == "optimized"
            if !valid then out := out.push ⟨joinPath path "phase", s!"subphase `{phaseTag.tag}` does not belong to `{tag.tag}` MIR"⟩
          | some (_, _) => out := out.push ⟨joinPath path "phase", "MIR subphase is not a typed tag"⟩
        | _ => pure ()
      if category == .withRetag then
        let performs := children.find? fun (key, _) => key == "performs_retag"
        match performs with
        | some (_, .scalar (.bool value)) =>
          if value != (tag.tag == "yes") then out := out.push ⟨joinPath path "performs_retag", "boolean disagrees with the WithRetag tag"⟩
        | _ => out := out.push ⟨joinPath path "performs_retag", "WithRetag tag is missing its boolean witness"⟩
      if category == .runtimeCheck then
        match children.find? fun (key, _) => key == "enabled" with
        | some (_, .scalar (.bool _)) => pure ()
        | _ => out := out.push ⟨joinPath path "enabled", "runtime-check tag is missing its configured boolean"⟩
      if category == .coverageKind then
        let hasNatField := fun key =>
          match children.find? fun (fieldKey, _) => fieldKey == key with
          | some (_, .scalar (.num value)) => ((Json.num value).getNat?).isOk
          | _ => false
        match tag.tag with
        | "point" =>
          match children.find? fun (key, _) => key == "point_kind" with
          | some (_, .enumTag .coveragePointKind _ _) => pure ()
          | _ => out := out.push ⟨joinPath path "point_kind", "coverage point is missing its typed point kind"⟩
          match children.find? fun (key, _) => key == "hir_id" with
          | some (_, .object fields) =>
            let hasOwner := fields.any fun (key, value) =>
              key == "owner_def_id" && match value with | .scalar (.str _) => true | _ => false
            let hasLocalId := fields.any fun (key, value) =>
              key == "local_id" && match value with
                | .scalar (.num number) => ((Json.num number).getNat?).isOk
                | _ => false
            if !hasOwner || !hasLocalId then
              out := out.push ⟨joinPath path "hir_id", "coverage point has malformed owner DefId or local HIR index"⟩
          | _ => out := out.push ⟨joinPath path "hir_id", "coverage point is missing its HIR identifier"⟩
        | "block_marker" =>
          if !hasNatField "id" then out := out.push ⟨joinPath path "id", "block-marker coverage is missing its identifier"⟩
        | "virtual_counter" =>
          if !hasNatField "bcb" then out := out.push ⟨joinPath path "bcb", "virtual-counter coverage is missing its basic-block counter"⟩
        | _ => pure ()
      if category == .regionKind then
        let hasField := fun key => (children.find? fun (fieldKey, _) => fieldKey == key).isSome
        match tag.tag with
        | "early_parameter" =>
          if !hasField "index" || !hasField "name" then
            out := out.push ⟨path, "early region parameter is missing its index or name"⟩
        | "bound" =>
          if !hasField "index_kind" || !hasField "variable_index" || !hasField "bound_kind" then
            out := out.push ⟨path, "bound region is missing index, variable, or bound-kind metadata"⟩
        | "late_parameter" =>
          if !hasField "scope_def_id" || !hasField "scope_def_path" || !hasField "parameter" then
            out := out.push ⟨path, "late region parameter is missing its scope or parameter metadata"⟩
        | "inference_variable" | "placeholder" =>
          if !hasField "index" && !hasField "universe" then
            out := out.push ⟨path, "region variable is missing its identifying metadata"⟩
        | _ => pure ()
      return out
  | .userTypeProjection projection => do
      let mut out := initial
      if let some issue := statusObligation? projection.status path then out := out.push issue
      if projection.status == .supported then
        if projection.baseIndex.isNone then
          out := out.push ⟨joinPath path "base_index", "supported user-type projection is missing its base annotation index"⟩
        if projection.projections.isNone then
          out := out.push ⟨joinPath path "projections", "supported user-type projection is missing its projection sequence"⟩
      match projection.projections with
      | some entries =>
        for (entry, index) in entries.toList.zipIdx do
          match entry with
          | .unknown tag => out := out.push (unknownTagObligation tag s!"{joinPath path "projections"}[{index}].kind")
          | _ => pure ()
      | none => pure ()
      return out
  | .array _ => return initial
  | .object fields => do
      let mut out := initial
      return out
  | .statement variant status fields => do
      let mut out := initial
      if let some issue := statusObligation? status path then out := out.push issue
      match variant with
      | .unknown tag => out := out.push (unknownTagObligation tag (joinPath path "variant"))
      | .ascribeUserType =>
        if status == .supported then
          if !(fields.any fun (key, value) => key == "user_type_projection" && match value with | .userTypeProjection _ => true | _ => false) then
            out := out.push ⟨joinPath path "user_type_projection", "supported AscribeUserType is missing typed projection data"⟩
          if !(fields.any fun (key, value) => key == "variance" && match value with | .enumTag .variance _ _ => true | _ => false) then
            out := out.push ⟨joinPath path "variance", "supported AscribeUserType is missing typed variance data"⟩
      | .coverage =>
        if status == .supported && !(fields.any fun (key, value) => key == "coverage" && match value with | .enumTag .coverageKind _ _ => true | _ => false) then
          out := out.push ⟨joinPath path "coverage", "supported Coverage statement is missing its typed coverage kind"⟩
      | _ => pure ()
      return out
  | .terminator variant status fields => do
      let mut out := initial
      if let some issue := statusObligation? status path then out := out.push issue
      match variant with
      | .unknown tag => out := out.push (unknownTagObligation tag (joinPath path "variant"))
      | _ => pure ()
      return out
  | .rvalue variant status fields => do
      let mut out := initial
      if let some issue := statusObligation? status path then out := out.push issue
      match variant with
      | .unknown tag => out := out.push (unknownTagObligation tag (joinPath path "kind"))
      | _ => pure ()
      return out
  | .operand variant status fields => do
      let mut out := initial
      if let some issue := statusObligation? status path then out := out.push issue
      match variant with
      | .unknown tag => out := out.push (unknownTagObligation tag (joinPath path "kind"))
      | _ => pure ()
      return out
  | .projection variant fields => do
      let mut out := initial
      match variant with
      | .unknown tag => out := out.push (unknownTagObligation tag (joinPath path "kind"))
      | _ => pure ()
      return out

private partial def valueObligationsInto (value : TypedValue) (path : String)
    (initial : Array Obligation) : Array Obligation := Id.run do
  let mut out := valueLocalObligationsInto value path initial
  match value with
  | .array values =>
    let mut index := 0
    for child in values do
      out := valueObligationsInto child s!"{path}[{index}]" out
      index := index + 1
  | .object fields | .enumTag _ _ fields | .statement _ _ fields | .terminator _ _ fields
  | .rvalue _ _ fields | .operand _ _ fields | .projection _ fields =>
    for (key, child) in fields do
      match value, key, child with
      | .enumTag _ _ _, "status", .scalar (.str text) =>
        if let some issue := statusObligation? (parseStatus text) (joinPath path key) then out := out.push issue
      | .enumTag _ _ _, "status", _ => out := out.push ⟨joinPath path key, "enum status must be a string"⟩
      | .object _, "status", .scalar (.str text) =>
        if let some issue := statusObligation? (parseStatus text) (joinPath path key) then out := out.push issue
      | .object _, "status", _ => out := out.push ⟨joinPath path key, "status field must be a string"⟩
      | _, _, _ => pure ()
      out := valueObligationsInto child (joinPath path key) out
  | _ => pure ()
  return out

private def valueObligations (value : TypedValue) (path : String) : Array Obligation :=
  valueObligationsInto value path #[]

private inductive RuntimeObligationSequence where
  | leaf (items : Array Obligation)
  | append (left right : RuntimeObligationSequence)
  | rebase (oldPath newPath : String) (inner : RuntimeObligationSequence)
  deriving Inhabited

private def appendRuntimeObligations (left right : Option RuntimeObligationSequence) :
    Option RuntimeObligationSequence :=
  match left, right with
  | none, right => right
  | left, none => left
  | some left, some right => some (.append left right)

private def rebaseRuntimeObligation (issue : Obligation) (oldPath newPath : String) : Obligation :=
  let path := if issue.path == oldPath then newPath else
    if issue.path.startsWith (oldPath ++ ".") || issue.path.startsWith (oldPath ++ "[") then
      newPath ++ String.ofList (issue.path.toList.drop oldPath.toList.length)
    else issue.path
  { issue with path := path }

private def flattenRuntimeObligations (sequence : Option RuntimeObligationSequence) : Array Obligation := Id.run do
  let mut pending : Array (RuntimeObligationSequence × Array (String × String)) := match sequence with
    | some sequence => #[(sequence, #[])]
    | none => #[]
  let mut result := #[]
  while h : pending.size > 0 do
    let (sequence, rebases) := pending[pending.size - 1]'(by omega)
    pending := pending.pop
    match sequence with
    | .leaf items =>
      for item in items do
        result := result.push (rebases.reverse.foldl (fun issue (oldPath, newPath) =>
          rebaseRuntimeObligation issue oldPath newPath) item)
    | .append left right =>
      pending := pending.push (right, rebases)
      pending := pending.push (left, rebases)
    | .rebase oldPath newPath inner =>
      pending := pending.push (inner, rebases.push (oldPath, newPath))
  return result

private structure RuntimeValueDecode where
  /-- Only the direct fields consumed by the parent's local invariants. -/
  summary : TypedValue
  obligations : Option RuntimeObligationSequence

private abbrev RuntimeDecodeCache := Std.HashMap DecodeValueKey (String × RuntimeValueDecode)

private def runtimeLocalObligations (value : TypedValue) (path : String)
    (children : Option RuntimeObligationSequence := none) : Option RuntimeObligationSequence :=
  let localIssues := valueLocalObligationsInto value path #[]
  if localIssues.isEmpty then children
  else appendRuntimeObligations (some (.leaf localIssues)) children

private initialize runtimeSummaryKeys : Std.HashSet String ← pure (Std.HashSet.ofList [
  "status", "phase", "performs_retag", "enabled", "point_kind", "hir_id",
  "id", "bcb", "index", "name", "index_kind", "variable_index",
  "bound_kind", "scope_def_id", "scope_def_path", "parameter", "universe",
  "base_index", "projections", "user_type_projection", "variance", "coverage"])

private def runtimeSummaryChild (key : String) (value : TypedValue) : TypedValue :=
  if key == "hir_id" then
    match value with
    | .object fields => .object (fields.filter fun (field, _) => field == "owner_def_id" || field == "local_id")
    | other => other
  else
    match value with
    | .enumTag category tag _ => .enumTag category tag #[]
    | .statement variant status _ => .statement variant status #[]
    | .terminator variant status _ => .terminator variant status #[]
    | .rvalue variant status _ => .rvalue variant status #[]
    | .operand variant status _ => .operand variant status #[]
    | .projection variant _ => .projection variant #[]
    | .object _ => .object #[]
    | .array _ => .array #[]
    | other => other

private abbrev RuntimeDecodeM := StateT RuntimeDecodeCache (Except String)

mutual
private partial def decodeRuntimeValueM (j : Json) (path : String) (domain : Domain)
    (tagCategory : Option TypedEnumTag) (memo : DecodeMemo) : RuntimeDecodeM RuntimeValueDecode := do
  let key := decodeValueKey j path domain tagCategory
  if let some (oldPath, decoded) := (← get).get? key then
    if oldPath == path then return decoded
    return { decoded with obligations := decoded.obligations.map fun issues => .rebase oldPath path issues }
  let decoded ← decodeRuntimeValueBody j path domain tagCategory memo
  modify fun cache => cache.insert key (path, decoded)
  return decoded

private partial def decodeRuntimeValueBody (j : Json) (path : String) (domain : Domain)
    (tagCategory : Option TypedEnumTag) (memo : DecodeMemo) : RuntimeDecodeM RuntimeValueDecode := do
  if let some id := isTypeRef j then
    let value := TypedValue.typeRef id
    return ⟨value, runtimeLocalObligations value path⟩
  if let some id := isAllocationRef j then
    let value := TypedValue.allocationRef id
    return ⟨value, runtimeLocalObligations value path⟩
  if statusOf? j == some "debug_payload" then
    let value := TypedValue.diagnostic j
    return ⟨value, runtimeLocalObligations value path⟩
  match j with
  | .arr values =>
    let mut obligations : Option RuntimeObligationSequence := none
    let mut index := 0
    for value in values do
      let child ← decodeRuntimeValueM value s!"{path}[{index}]" domain tagCategory memo
      obligations := appendRuntimeObligations obligations child.obligations
      index := index + 1
    let summary := TypedValue.array #[]
    return ⟨summary, runtimeLocalObligations summary path obligations⟩
  | .obj _ =>
    if isSourceSpanJson j then
      let value := TypedValue.sourceSpan (← parseSourceSpan j path memo)
      return ⟨value, runtimeLocalObligations value path⟩
    if hasField j "span" && hasField j "scope" then
      let value := TypedValue.sourceInfo (← parseSourceInfo j path memo)
      return ⟨value, runtimeLocalObligations value path⟩
    let effectiveDomain := if domain == .any then
      match recognizedAutoDomain j with | some detected => detected | none => .any
      else domain
    let fields ← objectFields j
    let parentTag := match effectiveDomain with
      | .rvalue | .operand | .statement | .terminator => domainTag j effectiveDomain
      | _ => none
    let mut summaries := #[]
    let mut obligations : Option RuntimeObligationSequence := none
    for (key, value) in fields do
      let childPath := joinPath path key
      let nextDomain := childDomain effectiveDomain key
      let child ← if key == "user_type_projection" && parentTag == some "AscribeUserType" then do
          let projection ← parseUserTypeProjection value childPath
          pure ⟨.userTypeProjection projection,
            runtimeLocalObligations (.userTypeProjection projection) childPath⟩
        else if key == "operator" && (parentTag == some "BinaryOp" || optionalField j "kind" == some (.str "Overflow")) then do
          let (tag, status) ← parseOperatorTag value childPath
          let decoded := match binOpFromExportTag tag with
            | some op => TypedValue.binOperator op status
            | none => TypedValue.unknownBinOperator tag status
          pure ⟨decoded, runtimeLocalObligations decoded childPath⟩
        else if key == "operator" && parentTag == some "UnaryOp" then do
          let (tag, status) ← parseOperatorTag value childPath
          let decoded := match unOpFromExportTag tag with
            | some op => TypedValue.unOperator op status
            | none => TypedValue.unknownUnOperator tag status
          pure ⟨decoded, runtimeLocalObligations decoded childPath⟩
        else decodeRuntimeValueM value childPath nextDomain (typedEnumCategory? key path parentTag value) memo
      let isTagField := match effectiveDomain with
        | .statement | .terminator | .rvalue | .operand | .projection => key == "status" || key == "variant" || key == "kind"
        | _ => false
      let parentIsTagged := match effectiveDomain with
        | .any | .statementWrapper | .terminatorWrapper => tagCategory.isSome
        | _ => false
      let parentIsObject := match effectiveDomain with
        | .any | .statementWrapper | .terminatorWrapper => !tagCategory.isSome
        | _ => false
      let statusIssues := if key == "status" && (parentIsTagged || parentIsObject) then
        match child.summary with
        | .scalar (.str text) => (statusObligation? (parseStatus text) childPath).toList
        | _ => [⟨childPath, if parentIsTagged then "enum status must be a string" else "status field must be a string"⟩]
        else []
      let statusSequence := if statusIssues.isEmpty then none else some (.leaf statusIssues.toArray)
      let childSequence := appendRuntimeObligations statusSequence child.obligations
      if !isTagField then obligations := appendRuntimeObligations obligations childSequence
      if !isTagField && (runtimeSummaryKeys.contains key ||
          path.endsWith ".hir_id" && (key == "owner_def_id" || key == "local_id")) then
        let childSummary := match key, value with
          | "instance_id", .num _ => match value.getNat? with
            | .ok id => TypedValue.instanceRef id
            | .error _ => runtimeSummaryChild key child.summary
          | "local", .num _ => match value.getNat? with
            | .ok id => TypedValue.localRef id
            | .error _ => runtimeSummaryChild key child.summary
          | "block", .num _ | "target", .num _ | "otherwise", .num _
          | "real_target", .num _ | "imaginary_target", .num _ | "resume", .num _ =>
            match value.getNat? with
            | .ok id => TypedValue.blockRef id
            | .error _ => runtimeSummaryChild key child.summary
          | _, _ => runtimeSummaryChild key child.summary
        summaries := summaries.push (key, childSummary)
    let summary ← match effectiveDomain with
      | .statement => do
        let tag ← fieldString j "variant" path
        let status := parseStatus (← fieldString j "status" path)
        pure (TypedValue.statement (statementVariant tag) status summaries)
      | .terminator => do
        let tag ← fieldString j "variant" path
        let status := parseStatus (← fieldString j "status" path)
        pure (TypedValue.terminator (terminatorVariant tag) status summaries)
      | .rvalue => do
        let tag ← fieldString j "kind" path
        let status := parseStatus (← fieldString j "status" path)
        if tag == "BinaryOp" || tag == "UnaryOp" then
          let operator ← field j "operator" path
          let _ ← parseOperatorTag operator (joinPath path "operator")
        pure (TypedValue.rvalue (rvalueVariant tag) status summaries)
      | .operand => do
        let tag ← fieldString j "kind" path
        let status := parseStatus (← fieldString j "status" path)
        pure (TypedValue.operand (operandVariant tag) status summaries)
      | .projection => do
        let tag ← fieldString j "kind" path
        pure (TypedValue.projection (projectionVariant tag) summaries)
      | .any | .statementWrapper | .terminatorWrapper => do
        match tagCategory with
        | some category => pure (TypedValue.enumTag category (← parseInlineTag j path) summaries)
        | none => pure (TypedValue.object summaries)
    return ⟨summary, runtimeLocalObligations summary path obligations⟩
  | .str _ =>
    match tagCategory with
    | some category =>
      let value := TypedValue.enumTag category (← parseInlineTag j path) #[]
      return ⟨value, runtimeLocalObligations value path⟩
    | none =>
      let value := TypedValue.scalar j
      return ⟨value, runtimeLocalObligations value path⟩
  | _ =>
    let value := TypedValue.scalar j
    return ⟨value, runtimeLocalObligations value path⟩
end

private def decodeRuntimeValue (j : Json) (path : String) (domain : Domain := .any)
    (tagCategory : Option TypedEnumTag := none) (memo : DecodeMemo := {}) : Except String RuntimeValueDecode := do
  (decodeRuntimeValueM j path domain tagCategory memo).run' {}

private def jsonArray (j : Json) (path : String) : Except String (Array Json) :=
  j.getArr? |>.mapError fun e => s!"{path}: expected array ({e})"

private def natArray (j : Json) (path : String) : Except String (Array Nat) := do
  let values ← jsonArray j path
  let mut out := #[]
  let mut index := 0
  for value in values do
    out := out.push (← value.getNat? |>.mapError fun e => s!"{path}[{index}]: expected unsigned integer ({e})")
    index := index + 1
  return out

private def optionalNat (j : Json) (key path : String) : Except String (Option Nat) := do
  match optionalField j key with
  | none | some .null => pure none
  | some value => (value.getNat?).map some |>.mapError fun e => s!"{joinPath path key}: expected unsigned integer or null ({e})"

private def optionalJson (j : Json) (key : String) : Option Json :=
  optionalField j key |>.filter (· != .null)

private def parseTagged (j : Json) (path : String) : Except String TaggedNode := do
  let tag ← fieldString j "kind" path
  let status ← match optionalField j "status" with
    | none => pure .supported
    | some value => parseStatus <$> (value.getStr? |>.mapError fun e => s!"{joinPath path "status"}: expected string ({e})")
  return ⟨status, tag, j⟩

private def parseAbiTag (j : Json) (path : String) : Except String TaggedNode := do
  match j with
  | .str tag => return ⟨.supported, tag, j⟩
  | .obj _ =>
    let tag ← match optionalField j "kind" with
      | some value => value.getStr? |>.mapError fun e => s!"{joinPath path "kind"}: expected string enum tag ({e})"
      | none => match optionalField j "variant" with
        | some value => value.getStr? |>.mapError fun e => s!"{joinPath path "variant"}: expected string enum tag ({e})"
        | none => throw s!"{path}: enum object is missing its kind tag"
    let status ← match optionalField j "status" with
      | none => pure .supported
      | some value => parseStatus <$> (value.getStr? |>.mapError fun e => s!"{joinPath path "status"}: expected string ({e})")
    return ⟨status, tag, j⟩
  | _ => throw s!"{path}: expected enum tag string or tagged object"

private def layoutVariantsKind (tag : String) : LayoutVariantsKind :=
  match tag with
  | "single" => .single
  | "multiple" => .multiple
  | "empty" => .empty
  | other => .unknown other

private def backendReprKind (tag : String) : BackendReprKind :=
  match tag with
  | "scalar" => .scalar
  | "scalar_pair" => .scalarPair
  | "memory" => .memory
  | "simd_vector" => .simdVector
  | "scalable_simd_vector" => .scalableSimdVector
  | other => .unknown other

private def optionalNatBefore (j : Json) (key path : String) : Except String (Option Nat) := do
  match optionalField j key with
  | none | some .null => pure none
  | some value => (value.getNat?).map some |>.mapError fun e => s!"{joinPath path key}: expected unsigned integer or null ({e})"

private def parsePrimitiveLayout (j : Json) (path : String) : Except String PrimitiveLayout := do
  let tag ← fieldString j "kind" path
  let kind := match tag with
    | "integer" => .integer
    | "float" => .float
    | "pointer" => .pointer
    | other => .unknown other
  let integerKindText ← optionalString j "integer_kind" path
  let integerKind := integerKindText.map integerTypeTag
  let signed ← match optionalField j "signed" with
    | none | some .null => pure none
    | some value => (value.getBool?).map some |>.mapError fun e => s!"{joinPath path "signed"}: expected boolean ({e})"
  let floatKindText ← optionalString j "float_kind" path
  let floatKind := floatKindText.map floatTypeTag
  let addressSpace ← optionalNatBefore j "address_space" path
  return {
    kind := kind
    sizeBytes := ← fieldNat j "size_bytes" path
    integerKind := integerKind
    signed := signed
    floatKind := floatKind
    addressSpace := addressSpace
    payload := j
  }

/-- Exact compiler u128 encoding; preserve legacy JSON naturals while allowing
full-width decimal strings that serde_json cannot represent as numbers. -/
private def parseU128Natural (j : Json) (path : String) : Except String Nat := do
  let value ← match j with
    | .str text => do
      unless !text.isEmpty && text.toList.all Char.isDigit do throw s!"{path}: expected exact unsigned decimal string"
      let some value := text.toNat? | throw s!"{path}: invalid unsigned decimal"
      pure value
    | _ => j.getNat? |>.mapError fun error => s!"{path}: expected unsigned integer ({error})"
  unless value < 2^128 do throw s!"{path}: u128 overflow"
  pure value

private def parseScalarLayout (j : Json) (path : String) : Except String ScalarLayout := do
  let tag ← fieldString j "kind" path
  let kind := match tag with
    | "initialized" => .initialized
    | "union" => .union
    | other => .unknown other
  let range ← match optionalJson j "valid_range" with
    | none => pure none
    | some value => pure (some (← parseU128Natural (← field value "start" (joinPath path "valid_range")) (joinPath path "valid_range.start"), ← parseU128Natural (← field value "end" (joinPath path "valid_range")) (joinPath path "valid_range.end")))
  return {
    kind := kind
    primitive := ← parsePrimitiveLayout (← field j "primitive" path) (joinPath path "primitive")
    validRange := range
    payload := j
  }

private def parseBackendRepr (j : Json) (path : String) : Except String BackendRepr := do
  let tag ← fieldString j "kind" path
  let kind := backendReprKind tag
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
    | none | some .null => pure none
    | some value => (value.getBool?).map some |>.mapError fun e => s!"{joinPath path "sized"}: expected boolean ({e})"
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
  | .unknown _ => pure ()
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
    payload := j
  }

private def parseFieldShape (j : Json) (path : String) : Except String FieldShape := do
  let tag ← fieldString j "kind" path
  let kind := match tag with
    | "primitive" => .primitive
    | "union" => .union
    | "array" => .array
    | "arbitrary" => .arbitrary
    | other => .unknown other
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
  | .unknown _ => pure ()
  return {
    kind := kind
    fieldCount := fieldCountValue
    offsetBytes := offsetBytes
    strideBytes := strideBytes
    offsetsBytes := offsetsBytes
    memoryOrder := memoryOrder
    payload := j
  }

private def parseLayoutVariant (j : Json) (path : String) : Except String LayoutVariant := do
  return {
    variantIndex := ← fieldNat j "variant_index" path
    sizeBytes := ← fieldNat j "size_bytes" path
    backendRepr := ← parseBackendRepr (← field j "backend_repr" path) (joinPath path "backend_repr")
    fieldOffsetsBytes := ← natArray (← field j "field_offsets_bytes" path) (joinPath path "field_offsets_bytes")
    uninhabited := ← fieldBool j "uninhabited" path
    payload := j
  }

private def decimalNat (text path : String) : Except String Nat := do
  if text.isEmpty then throw s!"{path}: expected a nonempty unsigned decimal integer"
  let mut value := 0
  for digit in text.toList do
    if digit < '0' || digit > '9' then throw s!"{path}: expected an unsigned decimal integer"
    value := value * 10 + digit.toNat - '0'.toNat
  return value

private def parseTagEncoding (j : Json) (path : String) : Except String TagEncoding := do
  match j with
  | .str legacy =>
    return ⟨.incomplete, .unknown s!"legacy_debug:{legacy}", none, none, none, j⟩
  | .obj _ =>
    let tag ← fieldString j "kind" path
    let status := parseStatus (← fieldString j "status" path)
    let kind := match tag with
      | "direct" => TagEncodingKind.direct
      | "niche" => TagEncodingKind.niche
      | other => TagEncodingKind.unknown other
    let untaggedVariant ← optionalNat j "untagged_variant" path
    let nicheVariants ← match optionalJson j "niche_variants" with
      | none => pure none
      | some range => pure (some (← fieldNat range "start" (joinPath path "niche_variants"), ← fieldNat range "end" (joinPath path "niche_variants")))
    let nicheStart ← match optionalField j "niche_start" with
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
    return ⟨status, kind, untaggedVariant, nicheVariants, nicheStart, j⟩
  | _ => throw s!"{path}: expected structured tag encoding"

private def parseVariantsLayout (j : Json) (path : String) : Except String VariantsLayout := do
  let tag ← fieldString j "kind" path
  let kind := layoutVariantsKind tag
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
  | .unknown _ => pure ()
  return {
    kind := kind
    variantIndex := variantIndex
    tag := scalarTag
    tagEncoding := tagEncoding
    tagFieldIndex := tagFieldIndex
    variants := variants
    payload := j
  }

private def parseLayoutUncached (j : Json) (path : String) : Except String Layout := do
  if (j.getObjVal? "$lean_miri_shared_ref").isOk then
    throw s!"{path}: shared layout reference requires a shared_payloads catalog"
  let statusText ← fieldString j "status" path
  let status := parseStatus statusText
  let kind := match asTag? j "kind" with
    | some "layout_query_error" => .layoutQueryError
    | some "layout" | none => .layout
    | some value => .unknown value
  let offsets ← if status == .supported then
    natArray (← field j "field_offsets_bytes" path) (joinPath path "field_offsets_bytes")
    else match optionalJson j "field_offsets_bytes" with
      | none => pure #[]
      | some value => natArray value (joinPath path "field_offsets_bytes")
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
  let variantsKind := variants.map fun value => layoutVariantsKind value.tag
  let backendReprKind := backend.map fun value => backendReprKind value.tag
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
    fieldOffsetsBytes := offsets
    fields := fields
    variantsLayout := variantsLayout
    backendRepresentation := backendRepresentation
    variantsKind := variantsKind
    backendReprKind := backendReprKind
    variants := variants
    backendRepr := backend
    payload := j
  }

private def parseLayout (j : Json) (path : String) (memo : DecodeMemo := {}) : Except String Layout := do
  match memo.layouts[j]? with
  | some value => pure value
  | none => parseLayoutUncached j path

private def isLayoutPayload (j : Json) : Bool :=
  hasField j "status" && hasField j "field_offsets_bytes"

private def collectSharedDecodeMemo (j : Json) (path : String) (memo : DecodeMemo)
    : DecodeMemo := Id.run do
  let key := j
  let mut memo := memo
  if isSourceSpanJson j && memo.sourceSpans[key]?.isNone then
    if let .ok value := parseSourceSpanUncached j path then
      memo := { memo with sourceSpans := memo.sourceSpans.insert key value }
  else if isLayoutPayload j && memo.layouts[key]?.isNone then
    if let .ok value := parseLayoutUncached j path then
      memo := { memo with layouts := memo.layouts.insert key value }
  return memo

private def sharedDecodeMemo (nodes : Array Json) : DecodeMemo := Id.run do
  let mut memo : DecodeMemo := {}
  for (node, index) in nodes.toList.zipIdx do
    memo := collectSharedDecodeMemo node s!"$.shared_payloads.nodes[{index}]" memo
  return memo

/-- JSON equality and hashing are only used as memo keys for canonical object
trees. In particular, never cache a Raw object whose inorder keys are not
strictly increasing, since malformed raw object trees can violate BEq symmetry. -/
private partial def hasCanonicalJsonObjectKeys : Json → Bool
  | .obj fields => Id.run do
    let mut previous? : Option String := none
    for (key, value) in fields.toList do
      if let some previous := previous? then
        unless previous < key do return false
      if !hasCanonicalJsonObjectKeys value then return false
      previous? := some key
    return true
  | .arr values => values.all hasCanonicalJsonObjectKeys
  | _ => true

private def compilerFunctionAbiDecodeMemo (nodes : Array Json) : DecodeMemo := Id.run do
  let mut memo : DecodeMemo := {}
  for (node, index) in nodes.toList.zipIdx do
    if !isSourceSpanJson node && isLayoutPayload node && hasCanonicalJsonObjectKeys node then
      if let .ok layout := parseLayoutUncached node s!"$.shared_payloads.nodes[{index}]" then
        memo := { memo with layouts := memo.layouts.insert node layout }
  return memo

/-- Opaque success-only layout memo for repeated decoding of compiler FnAbi
payloads from one shared-payload node table. The private constructor ensures
callers can prepare only the decoder's checked memo representation. -/
structure CompilerFunctionAbiMemo where
  private mk ::
  private memo : DecodeMemo

/-- Prepare a reusable FnAbi decoder memo from a runtime's shared payloads.
Malformed layouts are deliberately not cached, preserving occurrence paths. -/
def prepareCompilerFunctionAbiMemo (nodes : Array Json) : CompilerFunctionAbiMemo :=
  ⟨compilerFunctionAbiDecodeMemo nodes⟩

private def parseFunctionSignature (j : Json) (path : String) : Except String FunctionSignature := do
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
  let abiJson ← field j "abi" path
  let unwind ← match optionalField abiJson "unwind" with
    | none | some .null => pure none
    | some value => (value.getBool?).map some |>.mapError fun e => s!"{joinPath (joinPath path "abi") "unwind"}: expected boolean or null ({e})"
  let externAbi : ExternAbi := {
    kind := ← parseAbiTag abiJson (joinPath path "abi")
    unwind := unwind
    sourceSpelling := ← optionalString abiJson "source_spelling" (joinPath path "abi")
    payload := abiJson
  }
  return {
    inputs := inputs
    output := output
    safety := ← parseAbiTag (← field j "safety" path) (joinPath path "safety")
    abi := externAbi
    cVariadic := ← fieldBool j "c_variadic" path
  }

def decodeCompilerPredicateEvidence (j : Json) : Except String CompilerPredicateEvidence := do
  let normalization ← field j "normalization" "$predicate"
  let normalized ← match ← field normalization "value" "$predicate.normalization" with
    | .null => pure none
    | value => value.getNat?.map some
  pure {
    id := ← fieldNat j "predicate_id" "$predicate"
    typingEnvironment := ← fieldString j "typing_env" "$predicate"
    stableKey := ← fieldNat j "stable_key" "$predicate"
    autoTrait := ← fieldBool j "auto_trait" "$predicate"
    normalizationStatus := parseStatus (← fieldString normalization "status" "$predicate.normalization")
    normalizedId := normalized
    original := ← field j "original" "$predicate"
    payload := j }

/-- Decode all source PatternKind branches; unknown kinds fail explicitly. -/
partial def decodeCompilerPattern (j : Json) : Except String CompilerPattern := do
  unless (← fieldString j "status" "$pattern") == "supported" do throw "unsupported compiler pattern"
  match ← fieldString j "kind" "$pattern" with
  | "range" => return .range (← field j "start" "$pattern") (← field j "end" "$pattern")
  | "or" => return .or (← (← arrayField j "patterns" "$pattern").mapM decodeCompilerPattern)
  | "not_null" => pure .notNull
  | _ => throw "unknown compiler PatternKind"

/-- Preserve the compiler query's exact type and typing-environment key. -/
def decodeTypeCompilerFacts (j : Json) (path : String := "$compiler_facts") : Except String TypeCompilerFacts := do
  let some inputType := isTypeRef (← field j "input_type" path) | throw "compiler fact input_type is not a type reference"
  let mut booleans := #[]
  for (name,value) in ← objectFields (← field j "boolean_queries" path) do
    let result ← match ← field value "value" path with
      | .null => pure none
      | value => value.getBool?.map some
    booleans := booleans.push (name, {
      status := parseStatus (← fieldString value "status" path), value := result,
      reason := ← optionalString value "reason" path, payload := value })
  let mut types := #[]
  for (name,value) in ← objectFields (← field j "type_queries" path) do
    let result ← match ← field value "value" path with
      | .null => pure none
      | value => match isTypeRef value with
        | some id => pure (some id)
        | none => throw "compiler type query value is not a type reference or null"
    types := types.push (name, {
      status := parseStatus (← fieldString value "status" path), value := result,
      reason := ← optionalString value "reason" path, payload := value })
  let (captureNames,captureStatus) ← match optionalField j "capture_names" with
    | none => pure (none,none)
    | some query => do
      let status := parseStatus (← fieldString query "status" path)
      let names ← match ← field query "value" path with
        | .null => pure none
        | .arr names => (names.mapM fun (name : Json) => match name with
            | .null => pure none
            | name => name.getStr?.map some).map some
        | _ => throw "capture_names must be null or array"
      pure (names,some status)
  pure {
    captureNames := captureNames, captureNamesStatus := captureStatus,
    typingEnvironment := ← fieldString j "typing_env" path, inputTypeId := inputType,
    booleanQueries := booleans, typeQueries := types,
    adtPayload := match ← field j "adt" path with | .null => none | value => some value,
    payload := j }

private def parseTypeNode (j : Json) (path : String) (memo : DecodeMemo := {}) : Except String TypeNode := do
  let shape ← field j "shape" path
  let shapeStatus := parseStatus (← fieldString shape "status" (joinPath path "shape"))
  let shapeKindText ← fieldString shape "kind" (joinPath path "shape")
  let signedKindText ← optionalString shape "signed_kind" (joinPath path "shape")
  let unsignedKindText ← optionalString shape "unsigned_kind" (joinPath path "shape")
  let floatKindText ← optionalString shape "float_kind" (joinPath path "shape")
  let adtKindText ← optionalString shape "adt_kind" (joinPath path "shape")
  let shapeMetadata : TypeShapeMetadata := {
    signedKind := signedKindText.map integerTypeTag
    unsignedKind := unsignedKindText.map integerTypeTag
    floatKind := floatKindText.map floatTypeTag
    adtKind := adtKindText.map adtKindTag
  }
  let signature ← match optionalJson shape "signature" with
    | none => pure none
    | some signature => pure (some (← parseFunctionSignature signature (joinPath path "shape.signature")))
  return {
    pattern := ← match optionalField shape "pattern" with
      | none => pure none
      | some value => (decodeCompilerPattern value).map some
    compilerFacts := ← match optionalField j "compiler_facts" with
      | none => pure none
      | some value => (decodeTypeCompilerFacts value (joinPath path "compiler_facts")).map some
    id := ← fieldNat j "type_id" path
    display := ← fieldString j "display" path
    shapeStatus := shapeStatus
    shapeKind := typeShapeKind shapeKindText
    shapeMetadata := shapeMetadata
    signature := signature
    layout := ← parseLayout (← field j "layout" path) (joinPath path "layout") memo
    payload := j
  }

private def hexDigit (c : Char) : Bool :=
  c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

private def validHex (value : String) : Bool := value.toList.all hexDigit && value.length % 2 == 0

private def parseInitRange (j : Json) (path : String) : Except String InitRange := do
  let state ← fieldString j "state" path
  let initialized ← match state with
    | "initialized" => pure true
    | "uninitialized" => pure false
    | _ => throw s!"{joinPath path "state"}: unrecognized initialization state `{state}`"
  let first ← fieldNat j "start_bytes" path
  let last ← fieldNat j "end_bytes_exclusive" path
  if last < first then throw s!"{path}: initialization range has end before start"
  return ⟨initialized, first, last⟩

private def parseRelocation (j : Json) (path : String) : Except String Relocation := do
  let targetRef ← field j "target" path
  let target ← match isAllocationRef targetRef with
    | some id => pure id
    | none => throw s!"{joinPath path "target"}: expected allocation reference object"
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

private def parseAllocationMemory (j : Json) (path : String) : Except String AllocationMemory := do
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
    mutability := match ← fieldString j "mutability" path with
      | "mutable" => .mutable
      | "immutable" => .immutable
      | other => .unknown other
    bytesHex := bytes
    initializationRanges := ranges
    relocations := relocations
  }

private def allocationKind (kind : String) : AllocationKind :=
  match kind with
  | "memory" => .memory
  | "function" => .function
  | "static" => .static
  | "vtable" => .vtable
  | "type_id" => .typeId
  | "" => .unknown
  | other => .other other

private def parseDefinitionId (j : Json) (path : String) : Except String DefinitionId := do
  return ⟨← fieldNat j "crate" path, ← fieldNat j "index" path⟩

private def parseSelectedScope (j : Json) (path : String) : Except String SelectedScope := do
  let kind ← fieldString j "kind" path
  let statusText ← fieldString j "status" path
  let rootsJson ← arrayField j "roots" path
  let mut roots := #[]
  for (root, index) in rootsJson.toList.zipIdx do
    let rootPath := s!"{joinPath path "roots"}[{index}]"
    let defPath ← fieldString root "def_path" rootPath
    if defPath.isEmpty then throw s!"{joinPath rootPath "def_path"}: selected root path cannot be empty"
    roots := roots.push ⟨defPath, ← parseDefinitionId (← field root "def_id" rootPath) (joinPath rootPath "def_id")⟩
  if roots.toList.eraseDups.length != roots.size then throw s!"{joinPath path "roots"}: duplicate selected roots"
  let unresolvedJson ← arrayField j "unresolved_obligations" path
  let mut unresolved := #[]
  let mut evidence := #[]
  for (entry, index) in unresolvedJson.toList.zipIdx do
    let entryPath := s!"{joinPath path "unresolved_obligations"}[{index}]"
    match entry with
    | .str message =>
      unresolved := unresolved.push message
      evidence := evidence.push ⟨entryPath,message⟩
    | .obj _ =>
      let sourcePath ← fieldString entry "path" entryPath
      let status ← fieldString entry "status" entryPath
      let kind ← fieldString entry "kind" entryPath
      let reason ← fieldString entry "reason" entryPath
      let message := s!"{status} {kind}: {reason}"
      unresolved := unresolved.push message
      evidence := evidence.push ⟨sourcePath,message⟩
    | _ => throw s!"{entryPath}: expected string or structured source obligation"
  return {
    kind := kind
    statusText := statusText
    status := parseStatus statusText
    semantics := ← fieldString j "semantics" path
    roots := roots
    unresolvedObligations := unresolved
    unresolvedEvidence := evidence
    payload := j
  }

private def vtablePredicateKind (tag : String) : VtablePredicateKind :=
  match tag with
  | "trait" => .trait
  | "auto_trait" => .autoTrait
  | "projection" => .projection
  | other => .unknown other

private def parseVtablePredicate (j : Json) (path : String) : Except String VtablePredicate := do
  let tag ← fieldString j "kind" path
  let definitionId ← match optionalJson j "def_id" with
    | none => pure none
    | some value => pure (some (← parseDefinitionId value (joinPath path "def_id")))
  let definitionPath ← optionalString j "def_path" path
  let genericArgs ← match optionalJson j "generic_args" with
    | none => pure none
    | some value => pure (some (← decodeValue value (joinPath path "generic_args")))
  return {
    kind := vtablePredicateKind tag
    status := parseStatus (← fieldString j "status" path)
    definitionId := definitionId
    definitionPath := definitionPath
    genericArgs := genericArgs
    payload := j
  }

private def vtableEntryKind (tag : String) : VtableEntryKind :=
  match tag with
  | "drop_in_place_null" => .dropInPlaceNull
  | "drop_in_place" => .dropInPlace
  | "size_bytes" => .sizeBytes
  | "align_bytes" => .alignBytes
  | "vacant" => .vacant
  | "method" => .method
  | "supertrait_vtable_pointer" => .supertraitVtablePointer
  | other => .unknown other

private def parseVtableEntry (j : Json) (path : String) : Except String VtableEntry := do
  let tag ← fieldString j "kind" path
  let definitionId ← match optionalJson j "def_id" with
    | none => pure none
    | some value => pure (some (← parseDefinitionId value (joinPath path "def_id")))
  let traitDefinitionId ← match optionalJson j "trait_def_id" with
    | none => pure none
    | some value => pure (some (← parseDefinitionId value (joinPath path "trait_def_id")))
  let allocationId ← match optionalJson j "allocation" with
    | none => pure none
    | some value => match isAllocationRef value with
      | some id => pure (some id)
      | none => throw s!"{joinPath path "allocation"}: expected allocation reference"
  let genericArgs ← match optionalJson j "generic_args" with
    | none => pure none
    | some value => pure (some (← decodeValue value (joinPath path "generic_args")))
  return {
    kind := vtableEntryKind tag
    status := parseStatus (← fieldString j "status" path)
    instanceId := ← optionalNat j "instance_id" path
    definitionId := definitionId
    definitionPath := ← optionalString j "def_path" path
    allocationId := allocationId
    traitDefinitionId := traitDefinitionId
    traitDefinitionPath := ← optionalString j "trait_def_path" path
    genericArgs := genericArgs
    payload := j
  }

/-- Decode a source `tcx.vtable_entries` row retained outside a GlobalAlloc
image. Runtime-created vtables use this exact metadata without borrowing the
CTFE probe's allocation identity. -/
def decodeVtableEntry (j : Json) (path : String := "$compiler_vtable_entry") :
    Except String VtableEntry := parseVtableEntry j path

/-- Decode compiler-query static metadata, retaining the original evidence. -/
def decodeStaticGlobalInfo (j : Json) (path : String := "$static_global_info") : Except String StaticGlobalInfo := do
  return {
    status := parseStatus (← fieldString j "status" path)
    sizeBytes := ← fieldNat j "size_bytes" path
    alignBytes := ← fieldNat j "align_bytes" path
    mutability := match ← fieldString j "mutability" path with
      | "mutable" => .mutable
      | "immutable" => .immutable
      | tag => .unknown tag
    isStatic := ← fieldBool j "is_static" path
    foreignItem := ← fieldBool j "is_foreign_item" path
    threadLocal := ← fieldBool j "thread_local" path
    payload := j
  }

private def parseAllocation (j : Json) (path : String) : Except String AllocationNode := do
  let kindText ← fieldString j "kind" path
  let kind := allocationKind kindText
  let status := parseStatus (← fieldString j "status" path)
  let mut memory := none
  let mut data := none
  if status == .supported then
    match kind with
    | .memory =>
      let value ← parseAllocationMemory j path
      memory := some value
      data := some (.memory value)
    | .function =>
      let defId ← parseDefinitionId (← field j "instance_def_id" path) (joinPath path "instance_def_id")
      let args ← decodeValue (← field j "generic_args" path) (joinPath path "generic_args")
      data := some (.function {
        instanceId := ← fieldNat j "instance_id" path
        definitionId := defId
        definitionPath := ← fieldString j "instance_def_path" path
        genericArgs := args
        payload := j
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
        definitionId := ← parseDefinitionId (← field j "def_id" path) (joinPath path "def_id")
        definitionPath := ← fieldString j "def_path" path
        threadLocal := ← fieldBool j "thread_local" path
        initializer := initializer
        payload := j
      })
    | .vtable =>
      let predicatesJson ← arrayField j "predicates" path
      let entriesJson ← arrayField j "entries" path
      let mut predicates := #[]
      for (predicate, index) in predicatesJson.toList.zipIdx do
        predicates := predicates.push (← parseVtablePredicate predicate s!"{joinPath path "predicates"}[{index}]")
      let mut entries := #[]
      for (entry, index) in entriesJson.toList.zipIdx do
        entries := entries.push (← parseVtableEntry entry s!"{joinPath path "entries"}[{index}]")
      let typeRef ← field j "type" path
      let typeId ← match isTypeRef typeRef with
        | some id => pure id
        | none => throw s!"{joinPath path "type"}: expected type reference"
      data := some (.vtable {
        typeId := typeId
        sizeBytes := ← optionalNat j "size_bytes" path
        alignBytes := ← optionalNat j "align_bytes" path
        layoutStatus := parseStatus (← fieldString j "layout_status" path)
        predicates := predicates
        entries := entries
        payload := j
      })
    | .typeId =>
      let typeRef ← field j "type" path
      let typeId ← match isTypeRef typeRef with
        | some id => pure id
        | none => throw s!"{joinPath path "type"}: expected type reference"
      data := some (.typeId typeId)
    | .unknown | .other _ => pure ()
  return {
    id := ← fieldNat j "allocation_id" path
    sourceAllocId := ← do
      match ← optionalNat j "source_alloc_id" path with
      | none => pure none
      | some value =>
        if value == 0 || value >= 2^64 then
          throw s!"{joinPath path "source_alloc_id"}: expected a nonzero u64 rustc allocation identity"
        else pure (some (UInt64.ofNat value))
    status := status
    kind := kind
    memory := memory
    data := data
    payload := j
  }

private def parseSourceAllocIdKind (value path : String) : Except String SourceAllocIdKind := do
  match value with
  | "dangling" => pure .dangling
  | "memory" => pure .memory
  | "function" => pure .function
  | "vtable" => pure .vtable
  | "static" => pure .static
  | "type_id" => pure .typeId
  | _ => throw s!"{path}: unknown source AllocId kind `{value}`"

private def canonicalLowerHex (value : String) : Bool :=
  validHex value && value.toList.all (fun char =>
    (char >= '0' && char <= '9') || (char >= 'a' && char <= 'f'))

private def allocationNodeMatchesSourceKind (sourceKind : SourceAllocIdKind)
    (nodeKind : AllocationKind) : Bool :=
  match sourceKind, nodeKind with
  | .memory, .memory | .function, .function | .vtable, .vtable
  | .static, .static | .typeId, .typeId => true
  | .static, .other "static_initializer_error" => true
  | _, _ => false

private def parseSourceAllocIdDedupKind (value path : String) : Except String SourceAllocIdDedupKind := do
  match value with
  | "function" => pure .function
  | "vtable" => pure .vtable
  | "static" => pure .static
  | "type_id" => pure .typeId
  | "memory" | "memory_const_allocation" => pure .memory
  | "bytes" | "byte_memory" => pure .bytes
  | _ => throw s!"{path}: unknown source AllocId dedup key kind `{value}`"

private def parseSourceAllocIdPoolRow (j : Json) (path : String) : Except String SourceAllocIdPoolRow := do
  let raw ← fieldNat j "source_alloc_id" path
  if raw == 0 || raw >= 2^64 then throw s!"{joinPath path "source_alloc_id"}: expected nonzero u64"
  let kind ← parseSourceAllocIdKind (← fieldString j "kind" path) (joinPath path "kind")
  let status ← match ← fieldString j "status" path with
    | "dangling" => pure SourceAllocIdStatus.dangling
    | "serialized" => pure .serialized
    | "opaque" => pure .opaque
    | value => throw s!"{joinPath path "status"}: unknown source AllocId pool status `{value}`"
  let allocationId ← optionalNatField j "allocation_id" path
  let opaqueAllocationId ← optionalNat j "opaque_allocation_id" path
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
    | .dangling, .dangling, none => opaqueAllocationId.isNone
    | .memory, .serialized, some _ => opaqueAllocationId.isNone
    | .function, .serialized, some _ => opaqueAllocationId.isNone
    | .vtable, .serialized, some _ => opaqueAllocationId.isNone
    | .static, .serialized, some _ => opaqueAllocationId.isNone
    | .typeId, .serialized, some _ => opaqueAllocationId.isNone
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
  pure ⟨UInt64.ofNat raw, kind, status, allocationId, opaqueAllocationId, memoryMutability, memoryAlignBytes,
    memoryAllBytesInitialized, memoryHasProvenance, byteImageHex⟩

private def parseSourceAllocIdSaltResult (j : Json) (path : String) : Except String SourceAllocIdSaltResult := do
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

private def parseSourceAllocIdDedupRow (j : Json) (path : String) : Except String SourceAllocIdDedupRow := do
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

private def parseCompilerAllocIdWorld (j : Json) (nodes : Array AllocationNode) : Except String CompilerAllocIdWorld := do
  unless (← fieldString j "schema" "$.compiler_alloc_id_world") == "rustc_alloc_id_world_v1" do
    throw "$.compiler_alloc_id_world.schema: unsupported source AllocId world schema"
  unless (← fieldString j "profile" "$.compiler_alloc_id_world") == "prepared_post_export" do
    throw "$.compiler_alloc_id_world.profile: unsupported source AllocId world profile"
  let path := "$.compiler_alloc_id_world"
  let frontier ← field j "frontier" path
  let lastNat ← fieldNat frontier "last_reserved_source_alloc_id" (joinPath path "frontier")
  let nextNat ← fieldNat frontier "next_source_alloc_id" (joinPath path "frontier")
  let sentinelNat ← fieldNat frontier "final_sentinel_source_alloc_id" (joinPath path "frontier")
  if lastNat == 0 || lastNat >= 2^64 then throw "$.compiler_alloc_id_world.frontier.last_reserved_source_alloc_id: expected nonzero u64"
  if nextNat == 0 || nextNat >= 2^64 then throw "$.compiler_alloc_id_world.frontier.next_source_alloc_id: expected nonzero u64"
  unless sentinelNat == lastNat && nextNat == lastNat + 1 do
    throw "$.compiler_alloc_id_world.frontier: sentinel, last reservation, and next counter disagree"
  let poolThrough ← fieldNat j "global_pool_complete_through" path
  unless poolThrough == lastNat do throw "$.compiler_alloc_id_world.global_pool_complete_through: does not equal frontier"
  let poolJson ← arrayField j "raw_pool" path
  unless poolJson.size == lastNat do throw "$.compiler_alloc_id_world.raw_pool: must contain exactly the raw ID prefix 1..=frontier"
  let mut nodeIndexByGraphId : Std.HashMap Nat Nat := {}
  let mut nodeIndexBySourceId : Std.HashMap Nat Nat := {}
  for (node, index) in nodes.toList.zipIdx do
    if nodeIndexByGraphId.contains node.id then throw "$.compiler_alloc_id_world: duplicate allocation graph identity"
    nodeIndexByGraphId := nodeIndexByGraphId.insert node.id index
    if let some sourceId := node.sourceAllocId then
      if nodeIndexBySourceId.contains sourceId.toNat then
        throw "$.compiler_alloc_id_world: duplicate source AllocId witness on allocation nodes"
      nodeIndexBySourceId := nodeIndexBySourceId.insert sourceId.toNat index
  let mut pool := #[]
  for (value, index) in poolJson.toList.zipIdx do
    let rowPath := s!"$.compiler_alloc_id_world.raw_pool[{index}]"
    let row ← parseSourceAllocIdPoolRow value rowPath
    unless row.sourceAllocId.toNat == index + 1 do
      throw s!"{rowPath}.source_alloc_id: pool rows must be ordered and contiguous from one"
    if row.status == .serialized then
      let some graphId := row.allocationId | throw s!"{rowPath}: serialized pool row lacks graph identity"
      let some nodeIndex := nodeIndexByGraphId[graphId]? | throw s!"{rowPath}.allocation_id: allocation node is absent"
      let some node := nodes[nodeIndex]? | throw s!"{rowPath}.allocation_id: allocation node index is absent"
      unless node.sourceAllocId == some row.sourceAllocId do throw s!"{rowPath}: source AllocId disagrees with allocation node witness"
      unless node.status == .supported do throw s!"{rowPath}: serialized source global lacks supported allocation status"
      let expectedKind := match row.kind with
        | .memory => AllocationKind.memory
        | .function => .function
        | .vtable => .vtable
        | .static => .static
        | .typeId => .typeId
        | .dangling => .unknown
      unless node.kind == expectedKind do throw s!"{rowPath}: source global kind disagrees with allocation node"
      let expectedData : Bool := match row.kind, node.data with
        | .memory, some (.memory _) => true
        | .function, some (.function _) => true
        | .vtable, some (.vtable _) => true
        | .static, some (.static _) => true
        | .typeId, some (.typeId _) => true
        | _, _ => false
      unless expectedData do throw s!"{rowPath}: serialized source global lacks matching typed payload"
      if row.kind == .memory then
        let some projectionMutability := row.memoryMutability | throw s!"{rowPath}: memory projection mutability is absent"
        let some projectionAlign := row.memoryAlignBytes | throw s!"{rowPath}: memory projection alignment is absent"
        let some projectionInitialized := row.memoryAllBytesInitialized | throw s!"{rowPath}: memory projection initialization status is absent"
        let some projectionProvenance := row.memoryHasProvenance | throw s!"{rowPath}: memory projection provenance status is absent"
        let some (.memory image) := node.data | throw s!"{rowPath}: serialized memory node has no memory image"
        let actualMutability := image.mutability
        let actualInitialized := image.initializationRanges.all (·.initialized)
        let actualProvenance := !image.relocations.isEmpty
        unless projectionMutability == actualMutability && projectionAlign == image.alignBytes &&
            projectionInitialized == actualInitialized && projectionProvenance == actualProvenance do
          throw s!"{rowPath}: source byte-key projection disagrees with serialized memory image"
        let actualByteEligible := actualMutability == .immutable && image.alignBytes == 1 &&
          actualInitialized && !actualProvenance
        if actualByteEligible then
          unless row.byteImageHex == some image.bytesHex do
            throw s!"{rowPath}: eligible byte-memory projection differs from serialized bytes"
        else unless row.byteImageHex.isNone do
          throw s!"{rowPath}: ineligible memory image must not publish a byte key"
    else if let some graphId := row.opaqueAllocationId then
      unless row.status == .opaque do throw s!"{rowPath}.opaque_allocation_id: only valid for opaque rows"
      let some nodeIndex := nodeIndexByGraphId[graphId]? | throw s!"{rowPath}.opaque_allocation_id: allocation node is absent"
      let some node := nodes[nodeIndex]? | throw s!"{rowPath}.opaque_allocation_id: allocation node index is absent"
      unless node.sourceAllocId == some row.sourceAllocId && node.status != .supported &&
          allocationNodeMatchesSourceKind row.kind node.kind do
        throw s!"{rowPath}.opaque_allocation_id: source witness does not identify an unsupported allocation of the same source kind"
    else if nodeIndexBySourceId.contains row.sourceAllocId.toNat then
      throw s!"{rowPath}: non-serialized source ID is attached to an allocation node"
    pool := pool.push row
  let some sentinel := pool[pool.size - 1]? | throw "$.compiler_alloc_id_world.raw_pool: sentinel row absent"
  unless sentinel.kind == .dangling && sentinel.status == .dangling && sentinel.allocationId.isNone do
    throw "$.compiler_alloc_id_world.raw_pool: final reserved sentinel must be dangling"
  for node in nodes do
    let some sourceId := node.sourceAllocId | throw "$.compiler_alloc_id_world: every imported allocation must carry an exact source_alloc_id witness"
    let some row := pool[sourceId.toNat - 1]? | throw "$.compiler_alloc_id_world: allocation witness lies outside captured raw prefix"
    if node.status == .supported then
      unless row.status == .serialized && row.allocationId == some node.id do
        throw "$.compiler_alloc_id_world: supported allocation node is not covered by exactly one serialized pool row"
    else unless row.status == .opaque && row.opaqueAllocationId == some node.id do
      throw "$.compiler_alloc_id_world: unsupported allocation node is not covered by its opaque pool row"
  let dedupJson ← arrayField j "dedup_catalog" path
  let mut dedup := #[]
  let mut byteRowByImage : Std.HashMap String Nat := {}
  let mut functionRowByInstance : Std.HashMap InstanceId Nat := {}
  let mut vtableRowsByType : Std.HashMap TypeId (Array (Array VtablePredicate)) := {}
  let mut staticDefinitionsSeen : Std.HashMap (Nat × Nat) Nat := {}
  let mut typeIdRowByType : Std.HashMap TypeId Nat := {}
  for (value, index) in dedupJson.toList.zipIdx do
    let rowPath := s!"$.compiler_alloc_id_world.dedup_catalog[{index}]"
    let row ← parseSourceAllocIdDedupRow value rowPath
    unless #[.bytes, .function, .vtable, .static, .typeId].contains row.keyKind do
      throw s!"{rowPath}.key_kind: dedup key family is not available in this prepared profile"
    let some keyIndex := nodeIndexByGraphId[row.keyAllocationId]? | throw s!"{rowPath}.key_allocation_id: selected key node is not serialized"
    let some keyNode := nodes[keyIndex]? | throw s!"{rowPath}.key_allocation_id: selected key index is absent"
    let expectedKeyKind := match row.keyKind with
      | .bytes => AllocationKind.memory
      | .function => .function
      | .vtable => .vtable
      | .static => .static
      | .typeId => .typeId
      | _ => .unknown
    unless keyNode.kind == expectedKeyKind && keyNode.status == .supported do
      throw s!"{rowPath}: selected key node has incompatible kind/status"
    let expectedSaltCount := if row.keyKind == .static || row.keyKind == .typeId then 1 else 32
    unless row.salts.size == expectedSaltCount do
      throw s!"{rowPath}.salts: selected dedup key has the wrong number of source salt results"
    let mut seenResultAllocations : Std.HashMap Nat Bool := {}
    for (saltResult, saltIndex) in row.salts.toList.zipIdx do
      let expectedSalt := if row.keyKind == .static || row.keyKind == .typeId then 0 else saltIndex
      unless saltResult.salt == expectedSalt do
        throw s!"{rowPath}.salts[{saltIndex}].salt: unexpected source salt for selected dedup key"
      if seenResultAllocations.contains saltResult.allocationId then
        throw s!"{rowPath}.salts[{saltIndex}]: duplicate result allocation across source salts"
      seenResultAllocations := seenResultAllocations.insert saltResult.allocationId true
      let some poolRow := pool[saltResult.sourceAllocId.toNat - 1]? | throw s!"{rowPath}.salts: result AllocId outside captured pool"
      unless poolRow.status == .serialized && poolRow.allocationId == some saltResult.allocationId do
        throw s!"{rowPath}.salts: result must resolve to its unique serialized allocation node"
      let some resultIndex := nodeIndexByGraphId[saltResult.allocationId]?
        | throw s!"{rowPath}.salts[{saltIndex}]: result allocation node is absent"
      let some resultNode := nodes[resultIndex]?
        | throw s!"{rowPath}.salts[{saltIndex}]: result node index is absent"
      unless resultNode.kind == expectedKeyKind && resultNode.status == .supported do
        throw s!"{rowPath}.salts[{saltIndex}]: result allocation has incompatible kind/status"
      if row.keyKind == .function then
        let some (.function keyFunction) := keyNode.data
          | throw s!"{rowPath}: function key witness lacks typed instance data"
        let some (.function resultFunction) := resultNode.data
          | throw s!"{rowPath}.salts[{saltIndex}]: function result lacks typed instance data"
        unless keyFunction.instanceId == resultFunction.instanceId &&
            keyFunction.definitionId == resultFunction.definitionId &&
            keyFunction.genericArgs == resultFunction.genericArgs do
          throw s!"{rowPath}.salts[{saltIndex}]: function result does not match the exact selected Instance key"
      if row.keyKind == .vtable then
        let some (.vtable keyVtable) := keyNode.data
          | throw s!"{rowPath}: vtable key witness lacks typed identity data"
        let some (.vtable resultVtable) := resultNode.data
          | throw s!"{rowPath}.salts[{saltIndex}]: vtable result lacks typed identity data"
        unless keyVtable.typeId == resultVtable.typeId && keyVtable.predicates == resultVtable.predicates do
          throw s!"{rowPath}.salts[{saltIndex}]: vtable result does not match the exact selected type/predicate key"
      if row.keyKind == .static then
        let some (.static keyStatic) := keyNode.data
          | throw s!"{rowPath}: static key witness lacks typed DefId data"
        let some (.static resultStatic) := resultNode.data
          | throw s!"{rowPath}.salts[{saltIndex}]: static result lacks typed DefId data"
        unless keyStatic.definitionId == resultStatic.definitionId do
          throw s!"{rowPath}.salts[{saltIndex}]: static result does not match the exact selected DefId key"
        unless saltResult.salt == 0 && saltResult.allocationId == row.keyAllocationId do
          throw s!"{rowPath}: static key must provide its exact salt-zero typed witness"
      if row.keyKind == .typeId then
        let some (.typeId keyType) := keyNode.data
          | throw s!"{rowPath}: TypeId key witness lacks typed Ty data"
        let some (.typeId resultType) := resultNode.data
          | throw s!"{rowPath}.salts[{saltIndex}]: TypeId result lacks typed Ty data"
        unless keyType == resultType do
          throw s!"{rowPath}.salts[{saltIndex}]: TypeId result does not match the exact selected Ty key"
        unless saltResult.salt == 0 && saltResult.allocationId == row.keyAllocationId do
          throw s!"{rowPath}: TypeId key must provide its exact salt-zero typed witness"
    if row.keyKind == .bytes then
      let some imageHex := row.byteImageHex | throw s!"{rowPath}: byte key lacks its exact image"
      let some (.memory image) := keyNode.data | throw s!"{rowPath}: byte key node has no memory image"
      let some keySourceId := keyNode.sourceAllocId | throw s!"{rowPath}: byte key node lacks a source identity"
      let some keyPoolRow := pool[keySourceId.toNat - 1]? | throw s!"{rowPath}: byte key node is absent from the source pool"
      unless keyPoolRow.memoryMutability == some .immutable && keyPoolRow.memoryAlignBytes == some 1 &&
          keyPoolRow.memoryAllBytesInitialized == some true && keyPoolRow.memoryHasProvenance == some false &&
          keyPoolRow.byteImageHex == some imageHex && keyNode.memory == some image && image.bytesHex == imageHex &&
          image.mutability == .immutable && image.alignBytes == 1 && image.relocations.isEmpty &&
          image.initializationRanges.all (·.initialized) do
        throw s!"{rowPath}: byte key image is not the exact immutable aligned initialized provenance-free source key"
      for saltResult in row.salts do
        let some resultIndex := nodeIndexByGraphId[saltResult.allocationId]?
          | throw s!"{rowPath}.salts: byte-key result node is absent"
        let some resultNode := nodes[resultIndex]? | throw s!"{rowPath}.salts: result node index is absent"
        let some (.memory resultImage) := resultNode.data
          | throw s!"{rowPath}.salts: byte-key result is not a memory global"
        unless resultImage.bytesHex == imageHex && resultImage.alignBytes == 1 &&
            resultImage.mutability == .immutable && resultImage.relocations.isEmpty &&
            resultImage.initializationRanges.all (·.initialized) do
          throw s!"{rowPath}.salts: byte-key result does not contain the exact queried byte image"
      let some imageHex := row.byteImageHex | throw s!"{rowPath}: byte key lacks its exact image"
      if byteRowByImage.contains imageHex then throw s!"{rowPath}: duplicate exact byte-image key"
      byteRowByImage := byteRowByImage.insert imageHex dedup.size
    else if row.keyKind == .function then
      unless row.byteImageHex.isNone do throw s!"{rowPath}: typed function key carries an unexpected byte image"
      let some (.function keyFunction) := keyNode.data
        | throw s!"{rowPath}: function key witness lacks typed instance data"
      if functionRowByInstance.contains keyFunction.instanceId then
        throw s!"{rowPath}: duplicate exact function Instance key"
      unless (row.salts[0]?).map (·.allocationId) == some row.keyAllocationId do
        throw s!"{rowPath}: salt-zero function result is not its typed key witness"
      functionRowByInstance := functionRowByInstance.insert keyFunction.instanceId dedup.size
    else if row.keyKind == .vtable then
      unless row.byteImageHex.isNone do throw s!"{rowPath}: typed vtable key carries an unexpected byte image"
      let some (.vtable keyVtable) := keyNode.data
        | throw s!"{rowPath}: vtable key witness lacks typed identity data"
      let previous := vtableRowsByType[keyVtable.typeId]?.getD #[]
      if previous.contains keyVtable.predicates then
        throw s!"{rowPath}: duplicate exact compiler vtable type/predicate key"
      unless (row.salts[0]?).map (·.allocationId) == some row.keyAllocationId do
        throw s!"{rowPath}: salt-zero vtable result is not its typed key witness"
      vtableRowsByType := vtableRowsByType.insert keyVtable.typeId (previous.push keyVtable.predicates)
    else if row.keyKind == .static then
      unless row.byteImageHex.isNone do throw s!"{rowPath}: typed static key carries an unexpected byte image"
      let some (.static keyStatic) := keyNode.data
        | throw s!"{rowPath}: static key witness lacks typed DefId data"
      let defKey := (keyStatic.definitionId.crateIndex, keyStatic.definitionId.index)
      if staticDefinitionsSeen.contains defKey then
        throw s!"{rowPath}: duplicate exact static DefId key"
      unless (row.salts[0]?).map (·.allocationId) == some row.keyAllocationId do
        throw s!"{rowPath}: salt-zero static result is not its typed key witness"
      staticDefinitionsSeen := staticDefinitionsSeen.insert defKey dedup.size
    else
      unless row.byteImageHex.isNone do throw s!"{rowPath}: typed TypeId key carries an unexpected byte image"
      let some (.typeId keyType) := keyNode.data
        | throw s!"{rowPath}: TypeId key witness lacks typed Ty data"
      if typeIdRowByType.contains keyType then
        throw s!"{rowPath}: duplicate exact TypeId Ty key"
      unless (row.salts[0]?).map (·.allocationId) == some row.keyAllocationId do
        throw s!"{rowPath}: salt-zero TypeId result is not its typed key witness"
      typeIdRowByType := typeIdRowByType.insert keyType dedup.size
    dedup := dedup.push row
  for node in nodes do
    if node.status == .supported then
      if let some (.static static) := node.data then
        unless staticDefinitionsSeen.contains (static.definitionId.crateIndex, static.definitionId.index) do
          throw "$.compiler_alloc_id_world.dedup_catalog: selected source static node lacks its exact salt-zero key outcome"
      if let some (.typeId ty) := node.data then
        unless typeIdRowByType.contains ty do
          throw "$.compiler_alloc_id_world.dedup_catalog: selected TypeId node lacks its exact salt-zero key outcome"
  let mut completeFamilies := #[]
  let families ← arrayField j "complete_key_families" path
  for (family, index) in families.toList.zipIdx do
    let name ← family.getStr? |>.mapError fun _ => s!"$.compiler_alloc_id_world.complete_key_families[{index}]: expected string"
    unless name == "byte_memory" do
      throw s!"$.compiler_alloc_id_world.complete_key_families[{index}]: this decoder only recognizes the source-validated byte_memory family"
    let kind := SourceAllocIdDedupKind.bytes
    if completeFamilies.contains kind then throw "$.compiler_alloc_id_world.complete_key_families: duplicate key family"
    completeFamilies := completeFamilies.push kind
  unless completeFamilies.size == 1 && completeFamilies[0]? == some .bytes do
    throw "$.compiler_alloc_id_world.complete_key_families: prepared profile requires exactly byte_memory completeness"
  let unsupportedJson ← arrayField j "unsupported_key_families" path
  let mut unsupportedFamilies := #[]
  for (family, index) in unsupportedJson.toList.zipIdx do
    let name ← family.getStr? |>.mapError fun _ => s!"$.compiler_alloc_id_world.unsupported_key_families[{index}]: expected string"
    let kind ← parseSourceAllocIdDedupKind name s!"$.compiler_alloc_id_world.unsupported_key_families[{index}]"
    unless #[.function, .vtable, .static, .typeId, .memory].contains kind do
      throw s!"$.compiler_alloc_id_world.unsupported_key_families[{index}]: unknown or inapplicable unsupported family"
    if unsupportedFamilies.contains kind then throw "$.compiler_alloc_id_world.unsupported_key_families: duplicate family"
    if completeFamilies.contains kind then throw "$.compiler_alloc_id_world: key family is both complete and unsupported"
    unsupportedFamilies := unsupportedFamilies.push kind
  for required in #[SourceAllocIdDedupKind.function, .vtable, .static, .typeId, .memory] do
    unless unsupportedFamilies.contains required do
      throw "$.compiler_alloc_id_world.unsupported_key_families: function/vtable/static/type_id/memory_const_allocation must remain explicitly unsupported"
  for row in dedup do
    unless #[.bytes, .function, .vtable, .static, .typeId].contains row.keyKind do
      throw "$.compiler_alloc_id_world.dedup_catalog: unsupported selected key outcome family"
  if completeFamilies.contains .bytes then
    for row in pool do
      if row.kind == .memory then
        unless row.memoryMutability.isSome && row.memoryAlignBytes.isSome &&
            row.memoryAllBytesInitialized.isSome && row.memoryHasProvenance.isSome do
          throw "$.compiler_alloc_id_world.raw_pool: byte_memory completeness requires all source memory projection dimensions"
        let eligible := row.memoryMutability == some .immutable && row.memoryAlignBytes == some 1 &&
          row.memoryAllBytesInitialized == some true && row.memoryHasProvenance == some false
        if eligible then
          unless row.status == .serialized do
            throw "$.compiler_alloc_id_world.raw_pool: eligible byte-memory global is not serialized"
          let some imageHex := row.byteImageHex | throw "$.compiler_alloc_id_world.raw_pool: eligible byte key has no exact image"
          let some keyIndex := byteRowByImage[imageHex]? | throw "$.compiler_alloc_id_world.dedup_catalog: complete byte_memory family omits an eligible image"
          let some key := dedup[keyIndex]? | throw "$.compiler_alloc_id_world.dedup_catalog: key index is absent"
          unless key.salts.size == 32 && (List.range 32).all (fun salt => key.salts.any (·.salt == salt)) do
            throw "$.compiler_alloc_id_world.dedup_catalog: complete byte_memory family omits a full salt row for an eligible image"
  pure {
    lastReservedSourceAllocId := UInt64.ofNat lastNat
    nextSourceAllocId := UInt64.ofNat nextNat
    finalSentinelSourceAllocId := UInt64.ofNat sentinelNat
    rawPool := pool
    dedupCatalog := dedup
    completeKeyFamilies := completeFamilies
    unsupportedKeyFamilies := unsupportedFamilies
  }

/-- Revalidate allocation identity metadata against the exact retained raw
document. Public model records can be assembled or updated by callers, so the
prepared runtime must not trust the decoder's prior validation as a flag. -/
def validateCompilerAllocIdWorldRaw (raw : Json) (nodes : Array AllocationNode)
    (world : Option CompilerAllocIdWorld) : Except String Unit := do
  match optionalJson raw "compiler_alloc_id_world" with
  | none =>
    unless world.isNone do throw "source AllocId profile model is present but absent from its raw document"
  | some rawWorld =>
    let some world := world | throw "raw document contains a source AllocId profile absent from its typed model"
    let allocationsJson ← arrayField raw "allocations" "$"
    unless allocationsJson.size == nodes.size do
      throw "source AllocId profile no longer matches the raw allocation table"
    for (value, index) in allocationsJson.toList.zipIdx do
      let parsed ← parseAllocation value s!"$.allocations[{index}]"
      let some supplied := nodes[index]? | throw s!"$.allocations[{index}]: typed allocation row is absent"
      unless parsed.id == supplied.id && parsed.sourceAllocId == supplied.sourceAllocId &&
          parsed.status == supplied.status && parsed.kind == supplied.kind &&
          parsed.memory == supplied.memory && parsed.data == supplied.data &&
          parsed.payload.compress == supplied.payload.compress do
        throw s!"$.allocations[{index}]: source AllocId profile does not match the exact raw allocation node"
    let verified ← parseCompilerAllocIdWorld rawWorld nodes
    unless verified == world do
      throw "source AllocId profile model does not match its exact raw document object"

private def parseLocal (j : Json) (path : String) (memo : DecodeMemo := {}) : Except String LocalDecl := do
  let type ← field j "type" path
  let typeId ← match isTypeRef type with
    | some id => pure id
    | none => throw s!"{joinPath path "type"}: expected type reference object"
  let sourceInfo ← parseSourceInfo (← field j "source_info" path) (joinPath path "source_info") memo
  return {
    id := ← fieldNat j "local" path
    typeId := typeId
    sourceInfo := sourceInfo
    payload := j
  }

private def parseMirNode (wrapper : Json) (path : String) (domain : Domain) (memo : DecodeMemo := {}) : Except String MirNode := do
  let sourceInfo ← parseSourceInfo (← field wrapper "source_info" path) (joinPath path "source_info") memo
  let kind ← field wrapper "kind" path
  let value ← decodeValue kind (joinPath path "kind") domain .none memo
  return ⟨value, sourceInfo⟩

private def parseBasicBlock (j : Json) (path : String) (memo : DecodeMemo := {}) : Except String BasicBlock := do
  let statementJson ← arrayField j "statements" path
  let mut statements := #[]
  let mut index := 0
  for statement in statementJson do
    statements := statements.push (← parseMirNode statement s!"{joinPath path "statements"}[{index}]" .statement memo)
    index := index + 1
  let terminatorObject ← field j "terminator" path
  if terminatorObject == .null then throw s!"{joinPath path "terminator"}: basic block has no terminator"
  return {
    id := ← fieldNat j "block" path
    statements := statements
    terminator := ← parseMirNode terminatorObject (joinPath path "terminator") .terminator memo
    cleanup := ← fieldBool j "is_cleanup" path
    payload := j
  }

private def parseBodyCore (j : Json) (path fallbackName : String) (memo : DecodeMemo := {}) : Except String BodyCore := do
  let localsJson ← arrayField j "locals" path
  let mut locals := #[]
  let mut index := 0
  for localDecl in localsJson do
    locals := locals.push (← parseLocal localDecl s!"{joinPath path "locals"}[{index}]" memo)
    index := index + 1
  let blocksJson ← arrayField j "basic_blocks" path
  let mut blocks := #[]
  index := 0
  for block in blocksJson do
    blocks := blocks.push (← parseBasicBlock block s!"{joinPath path "basic_blocks"}[{index}]" memo)
    index := index + 1
  let defPath ← optionalString j "def_path" path
  let definitionId ← match optionalJson j "def_id" with
    | none => match optionalJson j "source_def_id" with
      | none => pure none
      | some value => pure (some (← parseDefinitionId value (joinPath path "source_def_id")))
    | some value => pure (some (← parseDefinitionId value (joinPath path "def_id")))
  let phase ← decodeValue (← field j "phase" path) (joinPath path "phase") .any (some .mirPhase) memo
  let injectionPhase ← match optionalJson j "injection_phase" with
    | none => pure none
    | some value => pure (some (← decodeValue value (joinPath path "injection_phase") .any (some .mirPhase) memo))
  let sourceScopes ← match optionalJson j "source_scopes" with
    | none => pure none
    | some value => some <$> jsonArray value (joinPath path "source_scopes")
  return {
    sourcePath := path
    defPath := match defPath with | some name => name | none => fallbackName
    definitionId := definitionId
    phase := phase
    injectionPhase := injectionPhase
    argumentCount := ← fieldNat j "arg_count" path
    spreadArgument := ← optionalNat j "spread_arg" path
    locals := locals
    blocks := blocks
    sourceScopes := sourceScopes
    payload := j
  }

private def parsePromotedBodies (j : Json) (path fallbackName : String) (memo : DecodeMemo := {}) : Except String (Array PromotedBody) := do
  let promotedJson ← match optionalJson j "promoted_bodies" with
    | none => pure #[]
    | some value => jsonArray value (joinPath path "promoted_bodies")
  let mut promotedBodies := #[]
  for (entry, index) in promotedJson.toList.zipIdx do
    let promotedPath := s!"{joinPath path "promoted_bodies"}[{index}]"
    let promotedIndex ← match optionalField entry "promoted_index" with
      | none => pure index
      | some value => value.getNat? |>.mapError fun e => s!"{joinPath promotedPath "promoted_index"}: expected unsigned integer ({e})"
    let status ← match optionalField entry "status" with
      | none => pure (if (optionalField entry "body").isSome then .supported else .incomplete)
      | some value => parseStatus <$> (value.getStr? |>.mapError fun e => s!"{joinPath promotedPath "status"}: expected string ({e})")
    let body ← match optionalJson entry "body" with
      | none => pure none
      | some value => pure (some (← parseBodyCore value (joinPath promotedPath "body") s!"{fallbackName}::promoted[{promotedIndex}]" memo))
    promotedBodies := promotedBodies.push ⟨promotedIndex, status, body, entry⟩
  return promotedBodies

private def parseBody (j : Json) (path fallbackName : String) (memo : DecodeMemo := {}) : Except String Body := do
  let core ← parseBodyCore j path fallbackName memo
  let promotedBodies ← parsePromotedBodies j path fallbackName memo
  return { core with promotedBodies := promotedBodies }

private def parseInstance (j : Json) (path : String) : Except String InstanceNode := do
  let kindText ← fieldString j "kind" path
  let kind := match kindText with
    | "instance_mir" => .instanceMir
    | "instance_mir_template" => .instanceMirTemplate
    | "intrinsic_without_mir" => .intrinsicWithoutMir
    | "intrinsic_dispatch" => .intrinsicDispatch
    | "foreign_item_no_mir" => .foreignItemNoMir
    | "virtual_dispatch" => .virtualDispatch
    | "virtual_dispatch_target" => .virtualDispatchTarget
    | "instance_mir_unavailable" => .instanceMirUnavailable
    | "symbol_identity_only" => .symbolIdentityOnly
    | other => .other other
  let id ← fieldNat j "instance_id" path
  let defPath ← optionalString j "def_path" path
  let definitionId ← match optionalJson j "def_id" with
    | none => pure none
    | some value => pure (some (← parseDefinitionId value (joinPath path "def_id")))
  let fallback := match defPath with
    | some value => value
    | none => s!"instance[{id}]"
  let bodyInstantiation ← match optionalJson j "body_instantiation" with
    | none => pure none
    | some value => pure (some (← parseAbiTag value (joinPath path "body_instantiation")))
  let bodyTemplateIsPolymorphic ← match optionalField j "body_template_is_polymorphic" with
    | none | some .null => pure none
    | some value => (value.getBool?).map some |>.mapError fun e => s!"{joinPath path "body_template_is_polymorphic"}: expected boolean ({e})"
  let instanceArgsAreMonomorphic ← match optionalField j "instance_args_are_monomorphic" with
    | none | some .null => pure none
    | some value => (value.getBool?).map some |>.mapError fun e => s!"{joinPath path "instance_args_are_monomorphic"}: expected boolean ({e})"
  let body ← match optionalJson j "body" with
    | none => pure none
    | some value => pure (some (← parseBody value (joinPath path "body") fallback))
  let promotedBodies ← parsePromotedBodies j path fallback
  return {
    id := id
    status := parseStatus (← fieldString j "status" path)
    kind := kind
    defPath := defPath
    definitionId := definitionId
    bodyInstantiation := bodyInstantiation
    bodyTemplateIsPolymorphic := bodyTemplateIsPolymorphic
    instanceArgsAreMonomorphic := instanceArgsAreMonomorphic
    body := body
    promotedBodies := promotedBodies
    payload := j
  }

private def passModeKind (tag : String) : PassModeKind :=
  match tag with
  | "Ignore" => .ignore
  | "Direct" => .direct
  | "Pair" => .pair
  | "Cast" => .cast
  | "Indirect" => .indirect
  | "IndirectUnsized" => .indirectUnsized
  | other => .unknown other

private def parseAbiAttributes (j : Json) (path : String) : Except String AbiAttributes := do
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
    argExtension := ← parseAbiTag (← field j "arg_extension" path) (joinPath path "arg_extension")
    captures := ← parseAbiTag (← field j "captures" path) (joinPath path "captures")
  }

private def abiRegisterKind (tag : String) : AbiRegisterKind :=
  match tag with
  | "integer" => .integer
  | "float" => .float
  | "ppc_f128" => .ppcF128
  | "vector" => .vector
  | other => .unknown other

private def canonicalAbiKind (tag : String) : CanonicalAbiKind :=
  match tag with
  | "c" => .c
  | "rust" => .rust
  | "rust_cold" => .rustCold
  | "rust_preserve_none" => .rustPreserveNone
  | "rust_tail" => .rustTail
  | "custom" => .custom
  | "swift" => .swift
  | "arm" => .arm
  | "gpu_kernel" => .gpuKernel
  | "interrupt" => .interrupt
  | "x86" => .x86
  | other => .unknown other

private def armCallKind (tag : String) : ArmCallKind :=
  match tag with
  | "aapcs" => .aapcs
  | "cmse_nonsecure_call" => .cmseNonSecureCall
  | "cmse_nonsecure_entry" => .cmseNonSecureEntry
  | other => .unknown other

private def interruptCallKind (tag : String) : InterruptCallKind :=
  match tag with
  | "avr" => .avr
  | "avr_non_blocking" => .avrNonBlocking
  | "msp430" => .msp430
  | "riscv_machine" => .riscvMachine
  | "riscv_supervisor" => .riscvSupervisor
  | "x86" => .x86
  | other => .unknown other

private def x86CallKind (tag : String) : X86CallKind :=
  match tag with
  | "fastcall" => .fastcall
  | "stdcall" => .stdcall
  | "sysv64" => .sysv64
  | "thiscall" => .thiscall
  | "vectorcall" => .vectorcall
  | "win64" => .win64
  | other => .unknown other

private def parseCanonicalAbi (j : Json) (path : String) : Except String CanonicalAbi := do
  let kindNode ← parseAbiTag j path
  return {
    status := kindNode.status
    kind := canonicalAbiKind kindNode.tag
    armCall := (← optionalString j "arm_call" path).map armCallKind
    interruptKind := (← optionalString j "interrupt_kind" path).map interruptCallKind
    x86Call := (← optionalString j "x86_call" path).map x86CallKind
    payload := j
  }

private def parseAbiRegister (j : Json) (path : String) : Except String AbiRegister := do
  let kindNode ← field j "kind" path
  let kindTag ← fieldString kindNode "kind" (joinPath path "kind")
  let hintElement ← match optionalJson kindNode "hint_element" with
    | none => pure none
    | some value => pure (some (← parseAbiTag value (joinPath path "kind.hint_element")))
  return {
    kind := abiRegisterKind kindTag
    sizeBits := ← fieldNat j "size_bits" path
    hintElement := hintElement
    payload := j
  }

private def parseAbiCastTarget (j : Json) (path : String) : Except String AbiCastTarget := do
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
    payload := j
  }

private def parseAbiPassMode (j : Json) (path : String) : Except String AbiPassMode := do
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
    | some value => pure (some (← parseAbiTag value (joinPath path "mode")))
  let padI32Count ← optionalNat j "pad_i32_count" path
  let addressSpace ← optionalNat j "address_space" path
  let kind := passModeKind tag
  match kind with
  | .cast => if castTarget.isNone || padI32Count.isNone then throw s!"{path}: Cast pass mode is missing target/padding data"
  | .indirect => if indirectMode.isNone then throw s!"{path}: Indirect pass mode is missing its mode tag"
  | .direct | .pair | .indirectUnsized | .ignore | .unknown _ => pure ()
  return {
    kind := kind
    attributes := attributes
    castTarget := castTarget
    padI32Count := padI32Count
    addressSpace := addressSpace
    indirectMode := indirectMode
    payload := j
  }

private def parseAbiArgument (j : Json) (path : String) (memo : DecodeMemo := {}) : Except String AbiArgument := do
  let typeRef ← field j "type" path
  let typeId ← match isTypeRef typeRef with
    | some id => pure id
    | none => throw s!"{joinPath path "type"}: expected type reference"
  let layout ← match optionalField j "layout" with
    | none => pure none
    | some value => pure (some (← parseLayout value (joinPath path "layout") memo))
  return {
    typeId := typeId
    layout := layout
    mode := ← parseAbiPassMode (← field j "mode" path) (joinPath path "mode")
    payload := j
  }

private def parseFunctionAbi (j : Json) (path : String) (memo : DecodeMemo := {}) : Except String FunctionAbi := do
  let argsJson ← arrayField j "arguments" path
  let mut args := #[]
  let mut index := 0
  for arg in argsJson do
    args := args.push (← parseAbiArgument arg s!"{joinPath path "arguments"}[{index}]" memo)
    index := index + 1
  let ret ← parseAbiArgument (← field j "return" path) (joinPath path "return") memo
  return {
    arguments := args
    returnValue := ret
    callingConvention := ← parseCanonicalAbi (← field j "calling_convention" path) (joinPath path "calling_convention")
    canUnwind := ← fieldBool j "can_unwind" path
    cVariadic := ← fieldBool j "c_variadic" path
    fixedCount := ← fieldNat j "fixed_count" path
    payload := j
  }

/-- Decode an exact compiler projection layout using the canonical schema. -/
def decodeCompilerLayout (j : Json) : Except String Layout :=
  parseLayout j "$.compiler_projection_layout"

/-- Decode an independently keyed compiler FnAbi query using the canonical schema. -/
def decodeCompilerFunctionAbi (j : Json) : Except String FunctionAbi :=
  parseFunctionAbi j "$.compiler_fn_abi"

/-- Decode a compiler FnAbi using successful layouts collected from the same
shared-payload table. Failures and diagnostics follow the uncached decoder. -/
def decodeCompilerFunctionAbiWithMemo (j : Json) (memo : CompilerFunctionAbiMemo) :
    Except String FunctionAbi :=
  parseFunctionAbi j "$.compiler_fn_abi" memo.memo

private partial def collectFunctionAbisAux (node : JsonTraversalCache.Node) (path : String) (memo : DecodeMemo)
    (seen : Std.HashSet JsonTraversalCache.Key := {}) (visited : Std.HashSet JsonTraversalCache.Key := {})
    : Except String (Array FunctionAbi × Std.HashSet JsonTraversalCache.Key × Std.HashSet JsonTraversalCache.Key) := do
  let j := node.value
  let key := node.key
  if statusOf? j == some "debug_payload" then return (#[], seen, visited)
  let isContainer := match j with | .arr _ | .obj _ => true | _ => false
  if isContainer && visited.contains key then return (#[], seen, visited)
  let visited := if isContainer then visited.insert key else visited
  match j with
  | .arr values =>
    let mut all := #[]
    let mut seen := seen
    let mut visited := visited
    let mut index := 0
    for value in values do
      let (found, nextSeen, nextVisited) ← collectFunctionAbisAux (node.child index value) s!"{path}[{index}]" memo seen visited
      all := all ++ found
      seen := nextSeen
      visited := nextVisited
      index := index + 1
    return (all, seen, visited)
  | .obj fields =>
    let mut all := #[]
    let mut seen := seen
    let mut visited := visited
    for ((fieldName, value), childIndex) in fields.toList.zipIdx do
      let child := node.child childIndex value
      if fieldName == "fn_abi" && value != .null then
        let query? ← match statusOf? value with
          | some "supported" => pure (some (← field value "value" (joinPath path fieldName)))
          | some _ => pure none
          | none => pure (some value)
        if let some queryValue := query? then
          let queryKey := (if statusOf? value == some "supported" then
              child.field "value" queryValue else child).key
          if !seen.contains queryKey then
            all := all.push (← parseFunctionAbi queryValue (joinPath (joinPath path fieldName) "value") memo)
            seen := seen.insert queryKey
      let looksLikeFunctionAbi :=
        hasField value "arguments" && hasField value "return" &&
        hasField value "calling_convention" && hasField value "can_unwind" &&
        hasField value "c_variadic" && hasField value "fixed_count"
      if looksLikeFunctionAbi && !seen.contains child.key then
        all := all.push (← parseFunctionAbi value (joinPath path fieldName) memo)
        seen := seen.insert child.key
      let (found, nextSeen, nextVisited) ← collectFunctionAbisAux child (joinPath path fieldName) memo seen visited
      all := all ++ found
      seen := nextSeen
      visited := nextVisited
    return (all, seen, visited)
  | _ => return (#[], seen, visited)

private def collectFunctionAbis (node : JsonTraversalCache.Node) (path : String) (memo : DecodeMemo := {}) : Except String (Array FunctionAbi) := do
  return (← collectFunctionAbisAux node path memo).1

private def validateDense (ids : Array Nat) (what : String) : Except String Unit := do
  let mut seen : Std.HashSet Nat := {}
  for id in ids do
    if seen.contains id then throw s!"{what}: duplicate IDs"
    seen := seen.insert id
  for id in ids do
    if id >= ids.size then throw s!"{what}: IDs must be dense from zero; found {id} with {ids.size} entries"

/-- The bounds encode ID membership only after all three source ID arrays pass
`validateDense`; each dense array then denotes exactly the natural range below
its size, independent of row order. -/
private partial def validateReferencesAux (node : JsonTraversalCache.Node) (path : String)
    (typeCount allocationCount instanceCount : Nat) (visited : Std.HashSet JsonTraversalCache.Key)
    : Except String (Std.HashSet JsonTraversalCache.Key) := do
  let j := node.value
  let memoKey := node.key
  if statusOf? j == some "debug_payload" then return visited
  let isContainer := match j with | .arr _ | .obj _ => true | _ => false
  if isContainer && visited.contains memoKey then return visited
  match j with
  | .arr values =>
    let mut index := 0
    let mut visited := visited
    for value in values do
      visited ← validateReferencesAux (node.child index value) s!"{path}[{index}]" typeCount allocationCount instanceCount visited
      index := index + 1
    return visited.insert memoKey
  | .obj fields =>
    let entries := fields.toList
    match entries with
    | [("type_id", idJson)] =>
      let id ← idJson.getNat? |>.mapError fun e => s!"{path}.type_id: malformed type reference ({e})"
      if id >= typeCount then throw s!"{path}: dangling type reference {id}"
      return visited.insert memoKey
    | [("allocation_id", idJson)] =>
      let id ← idJson.getNat? |>.mapError fun e => s!"{path}.allocation_id: malformed allocation reference ({e})"
      if id >= allocationCount then throw s!"{path}: dangling allocation reference {id}"
      return visited.insert memoKey
    | _ => pure ()
    let mut visited := visited
    for ((key, value), childIndex) in entries.zipIdx do
      if key == "instance_id" then
        let id ← value.getNat? |>.mapError fun e => s!"{joinPath path key}: malformed instance ID ({e})"
        if id >= instanceCount then throw s!"{joinPath path key}: dangling instance reference {id}"
      visited ← validateReferencesAux (node.child childIndex value) (joinPath path key) typeCount allocationCount instanceCount visited
    return visited.insert memoKey
  | _ => return visited

private def validateReferences (node : JsonTraversalCache.Node) (path : String)
    (typeCount allocationCount instanceCount : Nat) : Except String Unit := do
  let _ ← validateReferencesAux node path typeCount allocationCount instanceCount {}

private partial def validateMirIndices (j : Json) (path : String)
    (localCount : Nat) : Except String Unit := do
  if statusOf? j == some "debug_payload" then return
  match j with
  | .arr values =>
    let mut index := 0
    for value in values do
      validateMirIndices value s!"{path}[{index}]" localCount
      index := index + 1
  | .obj fields =>
    for (key, value) in fields.toList do
      if key == "local" then
        let id ← value.getNat? |>.mapError fun e => s!"{joinPath path key}: expected local index ({e})"
        if id >= localCount then throw s!"{joinPath path key}: local {id} is out of range (locals={localCount})"
      if key == "projection" then
        let projections ← value.getArr? |>.mapError fun e => s!"{joinPath path key}: expected projection array ({e})"
        for (projection, index) in projections.toList.zipIdx do
          let pPath := s!"{joinPath path key}[{index}]"
          let kind ← fieldString projection "kind" pPath
          if kind == "Index" then
            let id ← fieldNat projection "local" pPath
            if id >= localCount then throw s!"{pPath}.local: local {id} is out of range (locals={localCount})"
          if kind == "ConstantIndex" then
            let _ ← fieldNat projection "offset" pPath
            let _ ← fieldNat projection "min_length" pPath
            let _ ← fieldBool projection "from_end" pPath
          if kind == "Subslice" then
            let _ ← fieldNat projection "from" pPath
            let _ ← fieldNat projection "to" pPath
            let _ ← fieldBool projection "from_end" pPath
          if kind == "Field" then
            let _ ← fieldNat projection "index" pPath
            let _ ← field projection "field_type" pPath
          if kind == "Downcast" then
            let _ ← fieldNat projection "variant_index" pPath
          if kind == "OpaqueCast" then let _ ← field projection "cast_type" pPath
          if kind == "UnwrapUnsafeBinder" then let _ ← field projection "inner_type" pPath
          if isKnownProjection kind then let _ ← field projection "resulting_type" pPath
      validateMirIndices value (joinPath path key) localCount
  | _ => pure ()

private def checkBlockIndex (value : Json) (path : String) (blockCount : Nat) : Except String Unit := do
  let id ← value.getNat? |>.mapError fun e => s!"{path}: expected basic-block index ({e})"
  if id >= blockCount then throw s!"{path}: basic block {id} is out of range (blocks={blockCount})"

private def checkRequiredEdge (j : Json) (key path : String) (blockCount : Nat) : Except String Unit := do
  checkBlockIndex (← field j key path) (joinPath path key) blockCount

private def checkOptionalEdge (j : Json) (key path : String) (blockCount : Nat) : Except String Unit := do
  match optionalField j key with
  | none => throw s!"{path}: missing optional edge field `{key}`"
  | some .null => pure ()
  | some value => checkBlockIndex value (joinPath path key) blockCount

private def validateUnwind (j : Json) (path : String) (blockCount : Nat) : Except String Unit := do
  let kind ← fieldString j "kind" path
  if kind == "Cleanup" then checkRequiredEdge j "target" path blockCount

private def validateTerminatorEdges (j : Json) (path : String) (blockCount : Nat) : Except String Unit := do
  let variant ← fieldString j "variant" path
  match variant with
  | "Goto" => checkRequiredEdge j "target" path blockCount
  | "SwitchInt" =>
    checkRequiredEdge j "otherwise" path blockCount
    let targets ← arrayField j "targets" path
    for (target, index) in targets.toList.zipIdx do
      checkRequiredEdge target "target" s!"{joinPath path "targets"}[{index}]" blockCount
  | "Drop" =>
    checkRequiredEdge j "target" path blockCount
    checkOptionalEdge j "async_drop" path blockCount
    validateUnwind (← field j "unwind" path) (joinPath path "unwind") blockCount
  | "Call" =>
    checkOptionalEdge j "target" path blockCount
    validateUnwind (← field j "unwind" path) (joinPath path "unwind") blockCount
  | "Assert" =>
    checkRequiredEdge j "target" path blockCount
    validateUnwind (← field j "unwind" path) (joinPath path "unwind") blockCount
  | "Yield" =>
    checkRequiredEdge j "resume" path blockCount
    checkOptionalEdge j "drop" path blockCount
  | "FalseEdge" =>
    checkRequiredEdge j "real_target" path blockCount
    checkRequiredEdge j "imaginary_target" path blockCount
  | "FalseUnwind" =>
    checkRequiredEdge j "real_target" path blockCount
    validateUnwind (← field j "unwind" path) (joinPath path "unwind") blockCount
  | _ => pure ()

private def validateBody (j : Json) (path : String) : Except String Unit := do
  let locals ← arrayField j "locals" path
  let blocks ← arrayField j "basic_blocks" path
  if locals.isEmpty then throw s!"{joinPath path "locals"}: MIR body must declare the return local"
  if blocks.isEmpty then throw s!"{joinPath path "basic_blocks"}: MIR body must contain a start block"
  let mut index := 0
  for localDecl in locals do
    let id ← fieldNat localDecl "local" s!"{joinPath path "locals"}[{index}]"
    if id != index then throw s!"{joinPath path "locals"}[{index}]: local declarations must be densely ordered"
    index := index + 1
  index := 0
  for block in blocks do
    let blockPath := s!"{joinPath path "basic_blocks"}[{index}]"
    let id ← fieldNat block "block" blockPath
    if id != index then throw s!"{blockPath}: basic blocks must be densely ordered"
    let statements ← arrayField block "statements" blockPath
    for (statement, stmtIndex) in statements.toList.zipIdx do
      let kind ← field statement "kind" s!"{blockPath}.statements[{stmtIndex}]"
      validateMirIndices kind s!"{blockPath}.statements[{stmtIndex}].kind" locals.size
    let termWrapper ← field block "terminator" blockPath
    if termWrapper == .null then throw s!"{blockPath}: missing terminator"
    let term ← field termWrapper "kind" s!"{blockPath}.terminator"
    validateMirIndices term s!"{blockPath}.terminator.kind" locals.size
    validateTerminatorEdges term s!"{blockPath}.terminator.kind" blocks.size
    index := index + 1

private partial def validateAllBodiesAux (node : JsonTraversalCache.Node) (path : String) (visited : Std.HashSet JsonTraversalCache.Key)
    : Except String (Std.HashSet JsonTraversalCache.Key) := do
  let j := node.value
  let memoKey := node.key
  if statusOf? j == some "debug_payload" then return visited
  let isContainer := match j with | .arr _ | .obj _ => true | _ => false
  if isContainer && visited.contains memoKey then return visited
  match j with
  | .arr values =>
    let mut index := 0
    let mut visited := visited
    for value in values do
      visited ← validateAllBodiesAux (node.child index value) s!"{path}[{index}]" visited
      index := index + 1
    return visited.insert memoKey
  | .obj fields =>
    let hasLocals := (j.getObjVal? "locals").isOk
    let hasBlocks := (j.getObjVal? "basic_blocks").isOk
    if hasLocals != hasBlocks then throw s!"{path}: body requires both locals and basic_blocks"
    if hasLocals && hasBlocks then validateBody j path
    let mut visited := visited
    for ((key, value), childIndex) in fields.toList.zipIdx do
      visited ← validateAllBodiesAux (node.child childIndex value) (joinPath path key) visited
    return visited.insert memoKey
  | _ => return visited

private def validateAllBodies (node : JsonTraversalCache.Node) (path : String) : Except String Unit := do
  let _ ← validateAllBodiesAux node path {}

private def jsonToNatArray (nodes : Array α) (getId : α → Nat) : Array Nat := nodes.map getId

private def primitiveLayoutObligations (primitive : PrimitiveLayout) (path : String) : Array Obligation := Id.run do
  let mut issues := #[]
  match primitive.kind with
  | .unknown tag => issues := issues.push (unknownTagObligation tag (joinPath path "kind"))
  | .integer =>
    if primitive.integerKind.isNone || primitive.signed.isNone then
      issues := issues.push ⟨path, "integer primitive layout is missing integer kind or signedness"⟩
    match primitive.integerKind with
    | some (.unknown tag) => issues := issues.push (unknownTagObligation tag (joinPath path "integer_kind"))
    | _ => pure ()
  | .float =>
    if primitive.floatKind.isNone then issues := issues.push ⟨path, "float primitive layout is missing float kind"⟩
    match primitive.floatKind with
    | some (.unknown tag) => issues := issues.push (unknownTagObligation tag (joinPath path "float_kind"))
    | _ => pure ()
  | .pointer =>
    if primitive.addressSpace.isNone then issues := issues.push ⟨path, "pointer primitive layout is missing address space"⟩
  return issues

private def scalarLayoutObligations (scalar : ScalarLayout) (path : String) : Array Obligation := Id.run do
  let mut issues := primitiveLayoutObligations scalar.primitive (joinPath path "primitive")
  match scalar.kind with
  | .unknown tag => issues := issues.push (unknownTagObligation tag (joinPath path "kind"))
  | .initialized =>
    if scalar.validRange.isNone then issues := issues.push ⟨path, "initialized scalar layout is missing its valid range"⟩
  | .union => pure ()
  return issues

private def backendReprObligations (repr : BackendRepr) (path : String) : Array Obligation := Id.run do
  let mut issues := #[]
  match repr.kind with
  | .unknown tag => issues := issues.push (unknownTagObligation tag (joinPath path "kind"))
  | _ => pure ()
  for (key, scalar) in [("scalar", repr.scalar), ("first", repr.first), ("second", repr.second), ("element", repr.element)] do
    match scalar with
    | some value => issues := issues ++ scalarLayoutObligations value (joinPath path key)
    | none => pure ()
  return issues

private def taggedNodeObligations (node : TaggedNode) (known : List String)
    (path description : String) : Array Obligation := Id.run do
  let mut issues := (statusObligation? node.status path).toArray
  if !known.contains node.tag then
    issues := issues.push ⟨joinPath path "kind", s!"unrecognized {description} tag `{node.tag}`"⟩
  return issues

private def canonicalAbiObligations (abi : CanonicalAbi) (path : String) : Array Obligation := Id.run do
  let mut issues := (statusObligation? abi.status path).toArray
  match abi.kind with
  | .unknown tag => issues := issues.push (unknownTagObligation tag (joinPath path "kind"))
  | .arm =>
    match abi.armCall with
    | some (.unknown tag) => issues := issues.push (unknownTagObligation tag (joinPath path "arm_call"))
    | none => issues := issues.push ⟨joinPath path "arm_call", "ARM calling convention is missing its call kind"⟩
    | _ => pure ()
  | .interrupt =>
    match abi.interruptKind with
    | some (.unknown tag) => issues := issues.push (unknownTagObligation tag (joinPath path "interrupt_kind"))
    | none => issues := issues.push ⟨joinPath path "interrupt_kind", "interrupt calling convention is missing its interrupt kind"⟩
    | _ => pure ()
  | .x86 =>
    match abi.x86Call with
    | some (.unknown tag) => issues := issues.push (unknownTagObligation tag (joinPath path "x86_call"))
    | none => issues := issues.push ⟨joinPath path "x86_call", "x86 calling convention is missing its call kind"⟩
    | _ => pure ()
  | _ => pure ()
  return issues

private def externAbiObligations (abi : ExternAbi) (path : String) : Array Obligation := Id.run do
  let mut issues := taggedNodeObligations abi.kind
    ["c", "system", "rust", "rust_call", "rust_cold", "rust_invalid", "rust_preserve_none",
      "rust_tail", "llvm_intrinsic", "custom", "efi_api", "swift", "aapcs",
      "cmse_nonsecure_call", "cmse_nonsecure_entry", "gpu_kernel", "ptx_kernel",
      "avr_interrupt", "avr_non_blocking_interrupt", "msp430_interrupt",
      "riscv_interrupt_machine", "riscv_interrupt_supervisor", "x86_interrupt", "cdecl",
      "stdcall", "fastcall", "thiscall", "vectorcall", "sysv64", "win64"]
    path "extern ABI"
  let hasUnwindTag := ["c", "system", "aapcs", "cdecl", "stdcall", "fastcall", "thiscall", "vectorcall", "sysv64", "win64"].contains abi.kind.tag
  if hasUnwindTag && abi.unwind.isNone then
    issues := issues.push ⟨joinPath path "unwind", "this extern ABI requires an explicit unwind flag"⟩
  if !hasUnwindTag && abi.unwind.isSome then
    issues := issues.push ⟨joinPath path "unwind", "extern ABI has an unexpected unwind flag"⟩
  if abi.sourceSpelling.isNone then
    issues := issues.push ⟨joinPath path "source_spelling", "extern ABI is missing its original spelling"⟩
  return issues

private def abiAttributesObligations (attrs : AbiAttributes) (path : String) : Array Obligation := Id.run do
  let mut issues := taggedNodeObligations attrs.argExtension ["none", "zero_extend", "sign_extend"]
      (joinPath path "arg_extension") "argument extension"
  issues := issues ++ taggedNodeObligations attrs.captures ["none", "address", "read_only", "unrestricted"]
      (joinPath path "captures") "capture mode"
  return issues

private def abiRegisterObligations (reg : AbiRegister) (path : String) : Array Obligation := Id.run do
  let mut issues := #[]
  match reg.kind with
  | .unknown tag => issues := issues.push (unknownTagObligation tag (joinPath path "kind"))
  | .vector =>
    match reg.hintElement with
    | none => issues := issues.push ⟨joinPath path "kind.hint_element", "vector ABI register is missing its element hint"⟩
    | some hint => issues := issues ++ taggedNodeObligations hint ["integer", "float", "pointer"] (joinPath path "kind.hint_element") "register element"
  | _ => pure ()
  return issues

private def abiPassModeObligations (mode : AbiPassMode) (path : String) : Array Obligation := Id.run do
  let mut issues := #[]
  match mode.kind with
  | .unknown tag => issues := issues.push ⟨joinPath path "kind", s!"unrecognized ABI pass mode `{tag}`"⟩
  | _ => pure ()
  for (attrs, index) in mode.attributes.toList.zipIdx do
    issues := issues ++ abiAttributesObligations attrs s!"{path}.attributes[{index}]"
  match mode.castTarget with
  | some target =>
    for (register, index) in target.prefixRegisters.toList.zipIdx do
      issues := issues ++ abiRegisterObligations register s!"{path}.target.prefix_registers[{index}]"
    issues := issues ++ abiRegisterObligations target.restRegister (joinPath path "target.rest_register")
    issues := issues ++ abiAttributesObligations target.attributes (joinPath path "target.attributes")
  | none => pure ()
  match mode.indirectMode with
  | some tag => issues := issues ++ taggedNodeObligations tag ["pointer", "on_stack", "amdgpu_kernel_argument"] (joinPath path "mode") "indirect mode"
  | none => pure ()
  return issues

private def allocationMemoryObligations (memory : AllocationMemory) (path : String) : Array Obligation := Id.run do
  let mut issues := #[]
  match memory.mutability with
  | .unknown tag => issues := issues.push (unknownTagObligation tag (joinPath path "mutability"))
  | .mutable | .immutable => pure ()
  if memory.alignBytes == 0 then issues := issues.push ⟨joinPath path "align_bytes", "allocation alignment must be nonzero"⟩
  return issues

private def tagEncodingObligations (encoding : TagEncoding) (path : String) : Array Obligation := Id.run do
  let mut issues := (statusObligation? encoding.status path).toArray
  match encoding.kind with
  | .unknown tag => issues := issues.push (unknownTagObligation tag (joinPath path "kind"))
  | .direct => pure ()
  | .niche =>
    if encoding.untaggedVariant.isNone || encoding.nicheVariants.isNone || encoding.nicheStart.isNone then
      issues := issues.push ⟨path, "niche tag encoding is missing its structured variant range or niche start"⟩
    match encoding.nicheVariants with
    | some (first, last) => if last < first then issues := issues.push ⟨joinPath path "niche_variants", "inclusive niche range has its end before its start"⟩
    | none => pure ()
  return issues

private def promotedBodyObligations (promoted : Array PromotedBody) (path : String) : Array Obligation := Id.run do
  let mut issues := #[]
  for entry in promoted do
    if entry.body.isNone then
      issues := issues.push ⟨s!"{path}[{entry.index}]", "promoted MIR body is absent; cannot import it as typed MIR"⟩
    if entry.status != .supported then
      if let some issue := statusObligation? entry.status s!"{path}[{entry.index}].status" then
        issues := issues.push issue
  return issues

private def virtualIdentityObligations (raw : Json) (types : Array TypeNode)
    (instances : Array InstanceNode) : Array Obligation := Id.run do
  let mut issues := #[]
  for (node, index) in instances.toList.zipIdx do
    if node.kind != .virtualDispatchTarget || node.status != .supported then continue
    let base := s!"$.instances[{index}]"
    let payload := node.payload
    if (payload.getObjValAs? String "body_status").toOption != some "not_applicable" then
      issues := issues.push ⟨base ++ ".body_status", "virtual dispatch identity must explicitly have no executable MIR body"⟩
    if node.body.isSome then
      issues := issues.push ⟨base ++ ".body", "virtual dispatch identity cannot carry a fabricated MIR body"⟩
    let kind := (payload.getObjVal? "instance_kind").toOption.getD .null
    if (kind.getObjValAs? String "kind").toOption != some "virtual" then
      issues := issues.push ⟨base ++ ".instance_kind.kind", "virtual dispatch target must retain rustc InstanceKind::Virtual"⟩
    if (kind.getObjVal? "def_id").toOption != (payload.getObjVal? "def_id").toOption then
      issues := issues.push ⟨base ++ ".instance_kind.def_id", "virtual InstanceKind DefId disagrees with catalog DefId"⟩
    if (kind.getObjVal? "dispatch_slot").toOption != (payload.getObjVal? "dispatch_slot").toOption then
      issues := issues.push ⟨base ++ ".instance_kind.dispatch_slot", "virtual InstanceKind slot disagrees with catalog slot"⟩
    let identity := (payload.getObjVal? "virtual_identity").toOption.getD .null
    if (identity.getObjValAs? String "status").toOption != some "supported" then
      issues := issues.push ⟨base ++ ".virtual_identity.status", "virtual method identity/signature query is unresolved"⟩
    let functionType := (identity.getObjVal? "function_type").toOption.getD .null
    let typeId := (functionType.getObjValAs? Nat "type_id").toOption
    match typeId with
    | none => issues := issues.push ⟨base ++ ".virtual_identity.function_type", "virtual method identity is missing its compiler function type"⟩
    | some id =>
      let typeMatches := types.filter (·.id == id)
      if typeMatches.size != 1 then
        issues := issues.push ⟨base ++ ".virtual_identity.function_type", "virtual method identity references a missing or ambiguous type"⟩
      else if let some ty := typeMatches[0]? then
        if ty.shapeKind != .functionPointer && ty.shapeKind != .functionDefinition then
          issues := issues.push ⟨base ++ ".virtual_identity.function_type", "virtual method identity type is not a compiler function value"⟩
    let abi := (identity.getObjVal? "fn_abi").toOption.getD .null
    if (abi.getObjValAs? String "status").toOption != some "supported" then
      issues := issues.push ⟨base ++ ".virtual_identity.fn_abi.status", "virtual method FnAbi query is unresolved"⟩
    let abiValue := (abi.getObjVal? "value").toOption
    let catalog := ((raw.getObjVal? "compiler_instance_abis").bind Json.getArr?).toOption.getD #[]
    let abiRows := catalog.filter fun row =>
      (row.getObjValAs? Nat "instance_id").toOption == some node.id &&
      (row.getObjVal? "instance_kind").toOption == (payload.getObjVal? "instance_kind").toOption &&
      (row.getObjVal? "generic_args").toOption == (payload.getObjVal? "generic_args").toOption
    if abiRows.size != 1 then
      issues := issues.push ⟨base ++ ".virtual_identity.fn_abi", "virtual identity must match one exact full-instance FnAbi query"⟩
    else if let some row := abiRows[0]? then
      let query := (row.getObjVal? "abi_query").toOption.getD .null
      if (query.getObjValAs? String "status").toOption != some "supported" then
        issues := issues.push ⟨base ++ ".virtual_identity.fn_abi", "matching full-instance FnAbi query is unresolved"⟩
      else if abiValue != (query.getObjVal? "value").toOption then
        issues := issues.push ⟨base ++ ".virtual_identity.fn_abi", "virtual identity FnAbi disagrees with the exact full-instance FnAbi query"⟩
  return issues

private def extraSemanticObligations (raw : Json) (types : Array TypeNode) (allocations : Array AllocationNode)
    (instances : Array InstanceNode) (functionAbis : Array FunctionAbi) (bodies : Array Body) : Array Obligation := Id.run do
  let mut issues := #[]
  issues := issues ++ virtualIdentityObligations raw types instances
  for node in types do
    match node.shapeKind with
    | .unknown tag => issues := issues.push (unknownTagObligation tag s!"types[{node.id}].shape.kind")
    | _ => pure ()
    let shapePath := s!"types[{node.id}].shape"
    if node.shapeStatus == .supported then
      match node.shapeKind, node.shapeMetadata.signedKind, node.shapeMetadata.unsignedKind,
          node.shapeMetadata.floatKind, node.shapeMetadata.adtKind with
      | .int, none, _, _, _ => issues := issues.push ⟨joinPath shapePath "signed_kind", "signed integer type shape is missing its exact integer type"⟩
      | .int, some (.known kind), _, _, _ =>
        if !kind.signed then
          issues := issues.push ⟨joinPath shapePath "signed_kind", "signed integer type shape carries an unsigned integer kind"⟩
      | .uint, _, none, _, _ => issues := issues.push ⟨joinPath shapePath "unsigned_kind", "unsigned integer type shape is missing its exact integer type"⟩
      | .uint, _, some (.known kind), _, _ =>
        if kind.signed then
          issues := issues.push ⟨joinPath shapePath "unsigned_kind", "unsigned integer type shape carries a signed integer kind"⟩
      | .float, _, _, none, _ => issues := issues.push ⟨joinPath shapePath "float_kind", "float type shape is missing its exact float type"⟩
      | .adt, _, _, _, none => issues := issues.push ⟨joinPath shapePath "adt_kind", "ADT type shape is missing its struct/union/enum kind"⟩
      | _, _, _, _, _ => pure ()
    match node.shapeMetadata.signedKind with
    | some (.unknown tag) => issues := issues.push (unknownTagObligation tag (joinPath shapePath "signed_kind"))
    | _ => pure ()
    match node.shapeMetadata.unsignedKind with
    | some (.unknown tag) => issues := issues.push (unknownTagObligation tag (joinPath shapePath "unsigned_kind"))
    | _ => pure ()
    match node.shapeMetadata.floatKind with
    | some (.unknown tag) => issues := issues.push (unknownTagObligation tag (joinPath shapePath "float_kind"))
    | _ => pure ()
    match node.shapeMetadata.adtKind with
    | some (.unknown tag) => issues := issues.push (unknownTagObligation tag (joinPath shapePath "adt_kind"))
    | _ => pure ()
    match node.layout.kind with
    | .unknown tag => issues := issues.push (unknownTagObligation tag s!"types[{node.id}].layout.kind")
    | .layoutQueryError => issues := issues.push ⟨s!"types[{node.id}].layout", "rustc could not provide a concrete type layout"⟩
    | .layout => pure ()
    match node.layout.variantsKind with
    | some (.unknown tag) => issues := issues.push (unknownTagObligation tag s!"types[{node.id}].layout.variants.kind")
    | _ => pure ()
    match node.layout.backendReprKind with
    | some (.unknown tag) => issues := issues.push (unknownTagObligation tag s!"types[{node.id}].layout.backend_repr.kind")
    | _ => pure ()
    match node.layout.fields with
    | some fields =>
      match fields.kind with
      | .unknown tag => issues := issues.push (unknownTagObligation tag s!"types[{node.id}].layout.fields.kind")
      | _ => pure ()
    | none => pure ()
    match node.layout.backendRepresentation with
    | some repr => issues := issues ++ backendReprObligations repr s!"types[{node.id}].layout.backend_repr"
    | none => pure ()
    match node.layout.variantsLayout with
    | some variants =>
      match variants.kind with
      | .unknown tag => issues := issues.push (unknownTagObligation tag s!"types[{node.id}].layout.variants.kind")
      | _ => pure ()
      match variants.tagEncoding with
      | some encoding => issues := issues ++ tagEncodingObligations encoding s!"types[{node.id}].layout.variants.tag_encoding"
      | none => if variants.kind == .multiple then issues := issues.push ⟨s!"types[{node.id}].layout.variants.tag_encoding", "multi-variant layout is missing tag encoding"⟩
      match variants.tag with
      | some scalar => issues := issues ++ scalarLayoutObligations scalar s!"types[{node.id}].layout.variants.tag"
      | none => pure ()
      for variant in variants.variants do
        issues := issues ++ backendReprObligations variant.backendRepr s!"types[{node.id}].layout.variants[{variant.variantIndex}].backend_repr"
    | none => pure ()
    match node.signature with
    | some signature =>
      issues := issues ++ taggedNodeObligations signature.safety ["safe", "unsafe"]
        s!"types[{node.id}].shape.signature.safety" "function safety"
      issues := issues ++ externAbiObligations signature.abi s!"types[{node.id}].shape.signature.abi"
    | none => pure ()
  for node in allocations do
    let allocPath := s!"allocations[{node.id}]"
    match node.kind, node.data with
    | .unknown, _ => issues := issues.push ⟨s!"{allocPath}.kind", "allocation kind is missing"⟩
    | .other tag, _ => issues := issues.push ⟨s!"{allocPath}.kind", s!"unrecognized allocation kind `{tag}`"⟩
    | .memory, some (.memory memory) =>
      issues := issues ++ allocationMemoryObligations memory allocPath
    | .function, some (.function function) =>
      if function.definitionPath.isEmpty then issues := issues.push ⟨s!"{allocPath}.instance_def_path", "function allocation is missing its definition path"⟩
    | .static, some (.static static) =>
      if static.definitionPath.isEmpty then issues := issues.push ⟨s!"{allocPath}.def_path", "static allocation is missing its definition path"⟩
      match static.initializer, static.globalInfo with
      | some initializer, _ =>
        issues := issues ++ allocationMemoryObligations initializer (joinPath allocPath "initializer")
      | none, some info =>
        if !info.foreignItem then issues := issues.push ⟨joinPath allocPath "initializer", "non-foreign static is missing its initializer image"⟩
      | none, none =>
        issues := issues.push ⟨joinPath allocPath "initializer", "static without an initializer lacks exact foreign-item compiler evidence"⟩
    | .vtable, some (.vtable vtable) =>
      if let some issue := statusObligation? vtable.layoutStatus s!"{allocPath}.layout_status" then issues := issues.push issue
      for (predicate, index) in vtable.predicates.toList.zipIdx do
        let pPath := s!"{allocPath}.predicates[{index}]"
        if let some issue := statusObligation? predicate.status (joinPath pPath "status") then issues := issues.push issue
        match predicate.kind with
        | .unknown tag => issues := issues.push (unknownTagObligation tag (joinPath pPath "kind"))
        | _ => pure ()
      for (entry, index) in vtable.entries.toList.zipIdx do
        let ePath := s!"{allocPath}.entries[{index}]"
        if let some issue := statusObligation? entry.status (joinPath ePath "status") then issues := issues.push issue
        match entry.kind with
        | .unknown tag => issues := issues.push (unknownTagObligation tag (joinPath ePath "kind"))
        | _ => pure ()
    | .typeId, some (.typeId _) => pure ()
    | _, none => if node.status == .supported then issues := issues.push ⟨allocPath, "supported allocation is missing its typed payload"⟩
    | _, some _ => issues := issues.push ⟨allocPath, "allocation kind and typed payload disagree"⟩
  for node in instances do
    match node.kind with
    | .other tag => issues := issues.push ⟨s!"instances[{node.id}].kind", s!"unrecognized instance kind `{tag}`"⟩
    | .instanceMirTemplate => issues := issues.push ⟨s!"instances[{node.id}].kind", "generic MIR template is not a substituted executable instance body"⟩
    | .instanceMir =>
      if node.body.isNone then
        issues := issues.push ⟨s!"instances[{node.id}].body", "instance MIR is missing its decoded body"⟩
      match node.bodyInstantiation with
      | none => issues := issues.push ⟨s!"instances[{node.id}].body_instantiation", "instance body is missing substitution/normalization evidence"⟩
      | some detail =>
        if let some issue := statusObligation? detail.status s!"instances[{node.id}].body_instantiation.status" then issues := issues.push issue
        if detail.tag != "substituted_and_normalized" then
          issues := issues.push ⟨s!"instances[{node.id}].body_instantiation.kind", s!"unsupported instance body transformation `{detail.tag}`"⟩
      if node.bodyTemplateIsPolymorphic.isNone then
        issues := issues.push ⟨s!"instances[{node.id}].body_template_is_polymorphic", "instance lacks polymorphism metadata for its body template"⟩
      if node.instanceArgsAreMonomorphic != some true then
        issues := issues.push ⟨s!"instances[{node.id}].instance_args_are_monomorphic", "instance arguments are not known to be monomorphic"⟩
    | .intrinsicWithoutMir => issues := issues.push ⟨s!"instances[{node.id}]", "intrinsic instance has no imported MIR body"⟩
    | .intrinsicDispatch =>
      let base := s!"instances[{node.id}]"
      if node.status != .supported then
        issues := issues.push ⟨joinPath base "status", "intrinsic dispatch identity is not supported by the source compiler facts"⟩
      if node.body.isSome then
        issues := issues.push ⟨joinPath base "body", "intrinsic dispatch identity cannot carry fabricated MIR"⟩
      let instanceKind := (node.payload.getObjVal? "instance_kind").toOption.getD .null
      let tag := (instanceKind.getObjValAs? String "kind").toOption
      if tag != some "intrinsic" && tag != some "llvm_intrinsic" then
        issues := issues.push ⟨joinPath base "instance_kind.kind", "intrinsic dispatch requires exact rustc Intrinsic or LlvmIntrinsic identity"⟩
      let topDefId := node.definitionId
      let nestedDefIdJson := (instanceKind.getObjVal? "def_id").toOption
      let nestedDefId := nestedDefIdJson.bind fun value =>
        match value.getObjValAs? Nat "crate", value.getObjValAs? Nat "index" with
        | .ok crate, .ok index => some ⟨crate, index⟩
        | _, _ => none
      if topDefId.isNone then
        issues := issues.push ⟨joinPath base "def_id", "intrinsic dispatch requires an exact top-level rustc DefId"⟩
      if nestedDefId.isNone then
        issues := issues.push ⟨joinPath base "instance_kind.def_id", "intrinsic dispatch requires an exact nested rustc DefId"⟩
      if topDefId.isSome && nestedDefId.isSome && topDefId != nestedDefId then
        issues := issues.push ⟨joinPath base "instance_kind.def_id", "intrinsic identity DefId disagrees with its instance record"⟩
    | .foreignItemNoMir =>
      let base := s!"instances[{node.id}]"
      if node.status != .supported then
        issues := issues.push ⟨joinPath base "status", "foreign item dispatch identity is not supported by source compiler facts"⟩
      if node.body.isSome then
        issues := issues.push ⟨joinPath base "body", "foreign declaration cannot carry fabricated MIR"⟩
      if (node.payload.getObjValAs? Bool "foreign_item").toOption != some true then
        issues := issues.push ⟨joinPath base "foreign_item", "no-MIR foreign dispatch requires exact rustc is_foreign_item=true evidence"⟩
      let symbol := (node.payload.getObjVal? "symbol_name").toOption.getD .null
      if (symbol.getObjValAs? String "status").toOption != some "supported" ||
          ((symbol.getObjValAs? String "value").toOption.getD "").isEmpty then
        issues := issues.push ⟨joinPath base "symbol_name", "no-MIR foreign dispatch requires an exact nonempty rustc symbol name"⟩
      let instanceKind := (node.payload.getObjVal? "instance_kind").toOption.getD .null
      if (instanceKind.getObjValAs? String "kind").toOption != some "item" then
        issues := issues.push ⟨joinPath base "instance_kind.kind", "foreign dispatch requires exact rustc Item identity"⟩
      let topDefId := node.definitionId
      let nestedDefIdJson := (instanceKind.getObjVal? "def_id").toOption
      let nestedDefId := nestedDefIdJson.bind fun value =>
        match value.getObjValAs? Nat "crate", value.getObjValAs? Nat "index" with
        | .ok crate, .ok index => some ⟨crate, index⟩
        | _, _ => none
      if topDefId.isNone then
        issues := issues.push ⟨joinPath base "def_id", "foreign dispatch requires an exact top-level rustc DefId"⟩
      if nestedDefId.isNone then
        issues := issues.push ⟨joinPath base "instance_kind.def_id", "foreign dispatch requires an exact nested rustc DefId"⟩
      if topDefId.isSome && nestedDefId.isSome && topDefId != nestedDefId then
        issues := issues.push ⟨joinPath base "instance_kind.def_id", "foreign identity DefId disagrees with its instance record"⟩
    | .virtualDispatch => issues := issues.push ⟨s!"instances[{node.id}]", "virtual dispatch operation lacks a complete abstract instance identity"⟩
    | .virtualDispatchTarget => pure ()
    | .instanceMirUnavailable => issues := issues.push ⟨s!"instances[{node.id}]", "rustc did not provide an instance MIR body"⟩
    | .symbolIdentityOnly =>
      if node.body.isSome then
        issues := issues.push ⟨s!"instances[{node.id}].body", "symbol identity catalog row must not provide an executable MIR body"⟩
  for (abi, abiIndex) in functionAbis.toList.zipIdx do
    issues := issues ++ canonicalAbiObligations abi.callingConvention s!"function_abis[{abiIndex}].calling_convention"
    for (arg, argIndex) in (abi.arguments.push abi.returnValue).toList.zipIdx do
      issues := issues ++ abiPassModeObligations arg.mode s!"function_abis[{abiIndex}].arguments[{argIndex}].mode"
  for (body, index) in bodies.toList.zipIdx do
    issues := issues ++ promotedBodyObligations body.promotedBodies s!"bodies[{index}].promoted_bodies"
  for node in instances do
    issues := issues ++ promotedBodyObligations node.promotedBodies s!"instances[{node.id}].promoted_bodies"
  return issues

private def selectedScopeObligations (scope : SelectedScope) (bodies : Array Body)
    (instances : Array InstanceNode) : Array Obligation := Id.run do
  let mut issues := #[]
  if scope.kind != "rooted_structural_closure" then
    issues := issues.push ⟨"$.selected_scope.kind", s!"unrecognized selected-scope kind `{scope.kind}`"⟩
  if scope.statusText != "complete" || scope.status != .supported then
    issues := issues.push ⟨"$.selected_scope.status", s!"selected scope is not complete (`{scope.statusText}`)"⟩
  if scope.semantics != "structural_export_closure_only" then
    issues := issues.push ⟨"$.selected_scope.semantics", s!"unrecognized scope guarantee `{scope.semantics}`"⟩
  if scope.roots.isEmpty then issues := issues.push ⟨"$.selected_scope.roots", "selected structural closure has no root"⟩
  for (root, index) in scope.roots.toList.zipIdx do
    let resolvedBody := bodies.any fun body =>
      body.definitionId == some root.definitionId && body.defPath == root.defPath
    let resolvedInstance := instances.any fun inst =>
      inst.definitionId == some root.definitionId && inst.defPath == some root.defPath
    if !resolvedBody && !resolvedInstance then
      issues := issues.push ⟨s!"$.selected_scope.roots[{index}]", "selected DefId and path do not resolve to an emitted body or instance"⟩
  if scope.unresolvedEvidence.isEmpty then
    for (message, index) in scope.unresolvedObligations.toList.zipIdx do
      issues := issues.push ⟨s!"$.selected_scope.unresolved_obligations[{index}]", message⟩
  else issues := issues ++ scope.unresolvedEvidence
  return issues

private def globalCompletenessPath (path : String) : Bool :=
  path == "$.completeness.status" || path.startsWith "$.completeness.unresolved_obligations["

/-- Query demand belongs to the interpreter entry that performs it. A selected
MIR structural closure does not perform startup exported-symbol traversal or
arbitrary foreign-shim catalog queries. Unknown families remain structural. -/
private inductive QueryDependencyRole where
  | structural | foreignShim | programStartup | callHelper | runtimeCast | intrinsicValue
  | nativeCallbackSignature | runtimeTypeQuery | namedPathStatic | runtimeVirtual
  | runtimeCallMetadata
  deriving BEq

/-- Only the checked status of an actual array-entry query is demand-local.
Unknown descendants and malformed paths remain structural obligations. -/
private def exactCatalogStatus (path catalog suffix : String) : Bool :=
  match path.splitOn "[" with
  | [head, tail] =>
    match tail.splitOn "]" with
    | [index, ending] => head == "$." ++ catalog && !index.isEmpty &&
        index.toList.all (fun c => '0' ≤ c && c ≤ '9') &&
        (index == "0" || !index.startsWith "0") && ending == suffix
    | _ => false
  | _ => false

private def exactVirtualResolutionStatus (path : String) : Bool :=
  match path.splitOn "[" with
  | [head, tail] =>
    match tail.splitOn "]" with
    | [index, suffix] => head == "$.compiler_runtime_queries.virtual" &&
        !index.isEmpty && index.toList.all (fun c => '0' ≤ c && c ≤ '9') &&
        (index == "0" || !index.startsWith "0") && suffix == ".resolved.status"
    | _ => false
  | _ => false

private def exactRuntimeInstanceFactStatus (path : String) : Bool :=
  match path.splitOn "[" with
  | [head, tail] =>
    match tail.splitOn "]" with
    | [index, suffix] => head == "$.compiler_runtime_queries.instances" &&
        !index.isEmpty && index.toList.all (fun c => '0' ≤ c && c ≤ '9') &&
        (index == "0" || !index.startsWith "0") &&
        [".symbol_name.status", ".item_name.status", ".intrinsic_metadata.status",
          ".codegen_symbol_name.status"].contains suffix
    | _ => false
  | _ => false

private def exactLibcTypeLayoutStatus (path : String) : Bool :=
  let prefixText := "$.compiler_libc_type_layouts.entries."
  let suffixText := ".status"
  if !path.startsWith prefixText || !path.endsWith suffixText then false else
    let name := ((path.drop prefixText.length).dropEnd suffixText.length).toString
    let known := #[
      "_umtx_time", "addrinfo", "clockid_t", "dirent", "dirent64", "epoll_event",
      "iovec", "linger", "mach_timebase_info", "mode_t", "nfds_t", "off_t",
      "os_unfair_lock_s", "passwd", "pollfd", "pthread_attr_t", "pthread_cond_t",
      "pthread_condattr_t", "pthread_key_t", "pthread_mutex_t", "pthread_mutexattr_t",
      "pthread_rwlock_t", "pthread_t", "sa_family_t", "sem_t", "size_t", "sockaddr",
      "sockaddr_in", "sockaddr_in6", "sockaddr_storage", "socklen_t", "stack_t", "statx",
      "time_t", "timespec", "timeval", "timezone", "tm", "utsname", "wchar_t"]
    known.contains name && path == prefixText ++ name ++ suffixText

/-- These are the finite source-path type queries emitted by
`shim_abi::named_types`. Only their status leaves are demand-local; the
catalog payload and any unrecognized key remain structural evidence. -/
private def exactCompilerNamedTypeStatus (path : String) : Bool :=
  let prefixText := "$.compiler_named_types."
  let suffixText := ".status"
  if !path.startsWith prefixText || !path.endsWith suffixText then false else
    let key := ((path.drop prefixText.length).dropEnd suffixText.length).toString
    let known := #[
      "c_ulong", "off_t", "off64_t", "pid_t", "uid_t", "nfds_t",
      "wchar_t", "pthread_t", "pthread_key_t",
      "libc_c_void", "libc_c_void_pointer", "libc_c_char", "libc_c_char_pointer",
      "libc_sockaddr", "libc_sockaddr_pointer", "libc_timespec", "libc_timespec_pointer",
      "libc_socklen_t", "libc_socklen_t_pointer", "libc_iovec", "libc_iovec_pointer",
      "u32_pointer", "i32_pointer"]
    known.contains key && path == prefixText ++ key ++ suffixText

private def exactDropGlueStatus (path : String) : Bool :=
  let prefixText := "$.compiler_runtime_queries.types["
  if !path.startsWith prefixText then false else
    let rest := (path.drop prefixText.length).toString
    match rest.splitOn "]" with
    | [index, suffix] => !index.isEmpty && index.toList.all (fun c => '0' ≤ c && c ≤ '9') &&
        (index == "0" || !index.startsWith "0") && suffix == ".drop_glue.status"
    | _ => false

private def exactInstanceCatalogPath (path : String) : Bool := Id.run do
  let path := if path.startsWith "$." then (path.drop 2).toString else path
  if !path.startsWith "instances[" then return false
  let rest := (path.drop 10).toString
  let pieces := rest.splitOn "]"
  let [index, suffix] := pieces | return false
  if index.isEmpty || !index.toList.all (fun c => '0' ≤ c && c ≤ '9') ||
      (index != "0" && index.startsWith "0") then return false
  return suffix == "" || suffix == ".status"

/-- Type rows are a compilation-wide catalog, while a rooted export can use
only a small part of that catalog. These exact leaves are compiler queries
whose status is checked by the corresponding runtime adapter when requested.
The whitelist deliberately excludes shape data and unknown descendants.
Required layout status is elevated independently below; compiler facts remain
demand-local and are checked when their exact providers are requested.
-/
private def exactTypeQueryStatus (path : String) : Bool := Id.run do
  if !path.startsWith "$.types[" then return false
  let rest := (path.drop 8).toString
  let parts := rest.splitOn "]"
  let [index, suffix] := parts | return false
  if index.isEmpty || !index.toList.all (fun c => '0' ≤ c && c ≤ '9') ||
      (index != "0" && index.startsWith "0") then return false
  if suffix == ".layout.status" then return true
  let exactQueries := #[
    ".compiler_facts.type_id_hash.status",
    ".compiler_facts.discriminants.status",
    ".compiler_facts.projection_queries.status",
    ".compiler_facts.simd_size_and_type.status",
    ".compiler_facts.boolean_queries.is_unsafe_cell.status",
    ".compiler_facts.boolean_queries.has_erasable_regions.status",
    ".compiler_facts.boolean_queries.is_c_void.status",
    ".compiler_facts.boolean_queries.is_simd.status",
    ".compiler_facts.boolean_queries.is_box.status",
    ".compiler_facts.boolean_queries.is_global_box.status",
    ".compiler_facts.boolean_queries.is_dynamic.status",
    ".compiler_facts.boolean_queries.is_too_generic.status",
    ".compiler_facts.boolean_queries.is_monomorphic.status",
    ".compiler_facts.boolean_queries.is_monomorphic_enough.status",
    ".compiler_facts.boolean_queries.is_like_maybe_dangling.status",
    ".compiler_facts.boolean_queries.is_freeze.status",
    ".compiler_facts.boolean_queries.is_unpin.status",
    ".compiler_facts.boolean_queries.is_unsafe_unpin.status",
    ".compiler_facts.boolean_queries.needs_drop.status",
    ".compiler_facts.boolean_queries.opsem_inhabited.status",
    ".compiler_facts.boolean_queries.is_sized.status",
    ".compiler_facts.type_queries.discriminant_type.status",
    ".compiler_facts.type_queries.normalized.status",
    ".compiler_facts.type_queries.builtin_deref_explicit.status",
    ".compiler_facts.type_queries.builtin_deref_implicit.status",
    ".compiler_facts.type_queries.boxed_type.status",
    ".compiler_facts.type_queries.unsafe_binder_erased.status",
    ".compiler_facts.type_queries.metadata_tail.status",
    ".compiler_facts.type_queries.pointer_metadata_type.status"]
  return suffix == ".shape.constructor_identity.status" || exactQueries.contains suffix

/-- Compute the type rows structurally demanded by the selected source graph.
This is independent of `selected_scope.unresolved_obligations`, so editing a
root type's layout status without editing the producer's diagnostic list cannot
make that required layout disappear. References in compiler_facts are excluded:
they are separate compiler queries and are checked by their exact providers.
-/
private partial def collectGraphReferencesInto (j : Json)
    (result : Array (String × Nat)) : Array (String × Nat) := Id.run do
  match j with
  | .obj fields =>
    if (j.getObjValAs? String "status").toOption == some "debug_payload" then return result
    let mut result := result
    for (key, value) in fields.toList do
      if key == "normalization_template" || key == "compiler_facts" || key == "constructor_identity" then
        continue
      if key == "type_id" || key == "instance_id" || key == "allocation_id" then
        if let .ok id := value.getNat? then result := result.push (key,id)
      result := collectGraphReferencesInto value result
    return result
  | .arr values =>
    let mut result := result
    for value in values do result := collectGraphReferencesInto value result
    return result
  | _ => return result

private def collectGraphReferences (j : Json) : Array (String × Nat) :=
  collectGraphReferencesInto j #[]

private def rawArray (j : Json) (key : String) : Array Json :=
  ((j.getObjVal? key).bind Json.getArr?).toOption.getD #[]

private partial def collectThreadLocalRefsInto (j : Json) (path : String)
    (found : Array (String × Json)) : Array (String × Json) := Id.run do
  match j with
  | .obj fields =>
    if (j.getObjValAs? String "status").toOption == some "debug_payload" then return found
    let mut found := if (j.getObjValAs? String "kind").toOption == some "ThreadLocalRef" then found.push ⟨path,j⟩ else found
    for (key, value) in fields.toList do
      found := collectThreadLocalRefsInto value (joinPath path key) found
    return found
  | .arr values =>
    let mut found := found
    let mut index := 0
    for value in values do
      found := collectThreadLocalRefsInto value s!"{path}[{index}]" found
      index := index + 1
    return found
  | _ => return found

private def collectThreadLocalRefs (j : Json) (path : String) : Array (String × Json) :=
  collectThreadLocalRefsInto j path #[]

private structure RequiredStructuralDependencies where
  typeIds : Array Nat := #[]
  instanceIds : Array Nat := #[]
  allocationIds : Array Nat := #[]
  threadLocalRefs : Array (String × Json) := #[]

private def requiredStructuralDependencies (j : Json) (includeAllBodies : Bool := false) : RequiredStructuralDependencies := Id.run do
  let roots := match optionalField j "selected_scope" with
    | some scope => rawArray scope "roots"
    | none => #[]
  if roots.isEmpty && !includeAllBodies then return {}
  let bodyRows := rawArray j "bodies"
  let instanceRows := rawArray j "instances"
  let allocationRows := rawArray j "allocations"
  let typeRows := rawArray j "types"
  -- Hash only the exact source definition path string. Candidate rows are
  -- checked with Json equality below, so arbitrary malformed Json values do
  -- not rely on a Json hash/equality law.
  let mut bodiesByDefinitionPath : Std.HashMap (Option String) (Array (Json × Nat)) := {}
  let mut indexedBodyPosition := 0
  for body in bodyRows do
    let key := ((body.getObjVal? "def_path").toOption.bind fun value => (value.getStr?).toOption)
    bodiesByDefinitionPath := bodiesByDefinitionPath.insert key
      ((bodiesByDefinitionPath[key]?.getD #[]).push (body, indexedBodyPosition))
    indexedBodyPosition := indexedBodyPosition + 1
  let mut instancesByDefinitionPath : Std.HashMap (Option String) (Array (Json × Nat)) := {}
  let mut instancesById : Std.HashMap Nat Json := {}
  for inst in instanceRows do
    let key := ((inst.getObjVal? "def_path").toOption.bind fun value => (value.getStr?).toOption)
    if let .ok id := (inst.getObjVal? "instance_id").bind Json.getNat? then
      instancesByDefinitionPath := instancesByDefinitionPath.insert key
        ((instancesByDefinitionPath[key]?.getD #[]).push (inst, id))
      if !(instancesById[id]?.isSome) then instancesById := instancesById.insert id inst
  let mut typesById : Std.HashMap Nat Json := {}
  for row in typeRows do
    if let .ok id := (row.getObjVal? "type_id").bind Json.getNat? then
      if !(typesById[id]?.isSome) then typesById := typesById.insert id row
  let mut allocationsById : Std.HashMap Nat Json := {}
  for row in allocationRows do
    if let .ok id := (row.getObjVal? "allocation_id").bind Json.getNat? then
      if !(allocationsById[id]?.isSome) then allocationsById := allocationsById.insert id row
  let mut requiredTls := #[]
  let mut pendingInstances := #[]
  let mut pendingAllocations := #[]
  let mut pendingTypes := #[]
  let (selectedBodies, selectedInstances) := if includeAllBodies && (optionalField j "selected_scope").isNone then
      (bodyRows.toList.zipIdx.toArray, #[])
    else Id.run do
      let mut selected := #[]
      let mut rootInstances := #[]
      for root in roots do
        let rootPath := (root.getObjVal? "def_path").toOption
        let rootDef := (root.getObjVal? "def_id").toOption
        let rootPathText := rootPath.bind fun value => (value.getStr?).toOption
        let rootBodyRows := (bodiesByDefinitionPath[rootPathText]?.getD #[]).filter fun (body, _) =>
          (body.getObjVal? "def_path").toOption == rootPath &&
            (body.getObjVal? "def_id").toOption == rootDef
        -- The canonical root instance is an independent structural dependency,
        -- even when its MIR body is emitted and does not refer to itself.
        for (inst, id) in instancesByDefinitionPath[rootPathText]?.getD #[] do
          if (inst.getObjVal? "def_path").toOption == rootPath &&
              (inst.getObjVal? "def_id").toOption == rootDef then
            rootInstances := rootInstances.push id
        selected := selected ++ rootBodyRows
      (selected, rootInstances)
  pendingInstances := pendingInstances ++ selectedInstances
  for (body,bodyIndex) in selectedBodies do
      for reference in collectThreadLocalRefs body s!"$.bodies[{bodyIndex}]" do
        requiredTls := requiredTls.push reference
      for (kind,id) in collectGraphReferences body do
        if kind == "type_id" then pendingTypes := pendingTypes.push id
        else if kind == "instance_id" then pendingInstances := pendingInstances.push id
        else if kind == "allocation_id" then pendingAllocations := pendingAllocations.push id
  let mut visitedTypes := #[]
  let mut visitedTypeIds : Std.HashMap Nat Unit := {}
  let mut visitedInstances := #[]
  let mut visitedInstanceIds : Std.HashMap Nat Unit := {}
  let mut visitedAllocations := #[]
  let mut visitedAllocationIds : Std.HashMap Nat Unit := {}
  while !pendingTypes.isEmpty || !pendingInstances.isEmpty || !pendingAllocations.isEmpty do
    let typeRefs := pendingTypes
    pendingTypes := #[]
    for id in typeRefs do
      if visitedTypeIds[id]?.isSome then continue
      visitedTypes := visitedTypes.push id
      visitedTypeIds := visitedTypeIds.insert id ()
      if let some row := typesById[id]? then
        -- Only the compiler's source type shape participates here. Layout
        -- evidence itself is demanded separately; compiler_facts is a query catalog.
        if let .ok shape := row.getObjVal? "shape" then
          for (kind, child) in collectGraphReferences shape do
            if kind == "type_id" then pendingTypes := pendingTypes.push child
            else if kind == "instance_id" then pendingInstances := pendingInstances.push child
            else if kind == "allocation_id" then pendingAllocations := pendingAllocations.push child
    let instanceRefs := pendingInstances
    pendingInstances := #[]
    for id in instanceRefs do
      if visitedInstanceIds[id]?.isSome then continue
      visitedInstances := visitedInstances.push id
      visitedInstanceIds := visitedInstanceIds.insert id ()
      if let some row := instancesById[id]? then
        for reference in collectThreadLocalRefs row s!"$.instances[{id}]" do
          requiredTls := requiredTls.push reference
        for (key,child) in collectGraphReferences row do
          if key == "type_id" then pendingTypes := pendingTypes.push child
          if key == "instance_id" then pendingInstances := pendingInstances.push child
          if key == "allocation_id" then pendingAllocations := pendingAllocations.push child
    let allocationRefs := pendingAllocations
    pendingAllocations := #[]
    for id in allocationRefs do
      if visitedAllocationIds[id]?.isSome then continue
      visitedAllocations := visitedAllocations.push id
      visitedAllocationIds := visitedAllocationIds.insert id ()
      if let some row := allocationsById[id]? then
        for (key,child) in collectGraphReferences row do
          if key == "type_id" then pendingTypes := pendingTypes.push child
          if key == "instance_id" then pendingInstances := pendingInstances.push child
          if key == "allocation_id" then pendingAllocations := pendingAllocations.push child
  return ⟨visitedTypes, visitedInstances, visitedAllocations, requiredTls⟩

/-- The prepared allocator-world parser validates every field in its raw
subtree. Its opaque graph rows remain visible in the decoded tree, but only
rows reached from executable bodies are structural readiness blockers. -/
private def preparedWorldReadinessObligations (obligations : Array Obligation)
    (world : Option CompilerAllocIdWorld) (allocations : Array AllocationNode)
    (requiredAllocationIds : Array Nat) : Array Obligation := Id.run do
  let some world := world | return obligations
  let mut requiredIds : Std.HashMap Nat Unit := {}
  for allocationId in requiredAllocationIds do
    requiredIds := requiredIds.insert allocationId ()
  let mut undemandedOpaqueIds : Std.HashMap Nat Unit := {}
  for row in world.rawPool do
    if row.status == .opaque then
      if let some allocationId := row.opaqueAllocationId then
        if !requiredIds.contains allocationId then
          undemandedOpaqueIds := undemandedOpaqueIds.insert allocationId ()
  let mut undemandedOpaqueIndexes : Std.HashMap Nat Unit := {}
  for (node, index) in allocations.toList.zipIdx do
    if undemandedOpaqueIds.contains node.id then
      undemandedOpaqueIndexes := undemandedOpaqueIndexes.insert index ()
  obligations.filter fun issue => Id.run do
    if issue.path.startsWith "$.compiler_alloc_id_world." then return false
    let arrayPrefix := "$.allocations["
    if issue.path.startsWith arrayPrefix then
      let rest := (issue.path.drop arrayPrefix.length).toString
      let indexText := (rest.takeWhile (· != ']')).toString
      if rest.startsWith (indexText ++ "]") then
        if let .ok index := decimalNat indexText issue.path then
          if undemandedOpaqueIndexes.contains index then return false
    let semanticPrefix := "allocations["
    if issue.path.startsWith semanticPrefix then
      let rest := (issue.path.drop semanticPrefix.length).toString
      let allocationText := (rest.takeWhile (· != ']')).toString
      if rest.startsWith (allocationText ++ "]") then
        if let .ok allocationId := decimalNat allocationText issue.path then
          if undemandedOpaqueIds.contains allocationId then return false
    return true

/-- Symbol-only entries close compiler identity references but carry no MIR.
Their absence of a body is harmless while they are unused catalog rows, but
any row reached from a selected root or executable graph is an unresolved
structural dependency. -/
private def requiredIdentityOnlyInstanceObligations (instances : Array InstanceNode)
    (requiredIds : Array Nat) : Array Obligation := Id.run do
  let mut issues := #[]
  for (node, index) in instances.toList.zipIdx do
    if requiredIds.contains node.id && node.kind == .symbolIdentityOnly then
      issues := issues.push ⟨s!"$.instances[{index}].kind",
        "selected execution depends on a symbol identity that has no imported MIR body"⟩
  return issues

private def threadLocalShapeObligations (references : Array (String × Json)) : Array Obligation := Id.run do
  let mut issues := #[]
  for (path, value) in references do
    unless (value.getObjValAs? String "status").toOption == some "supported" do continue
    let definition := (value.getObjVal? "def_id").toOption
    match definition with
    | none => issues := issues.push ⟨joinPath path "def_id", "supported ThreadLocalRef is missing its exact compiler DefId"⟩
    | some defId =>
      for key in ["crate", "index"] do
        if ((defId.getObjVal? key).bind Json.getNat?).toOption.isNone then
          issues := issues.push ⟨joinPath (joinPath path "def_id") key, "ThreadLocalRef DefId component must be an unsigned integer"⟩
    let info := (value.getObjVal? "global_info").toOption
    let mut foreign := false
    match info with
    | none => issues := issues.push ⟨joinPath path "global_info", "supported ThreadLocalRef is missing static compiler query evidence"⟩
    | some info =>
      if (info.getObjValAs? String "status").toOption != some "supported" then
        issues := issues.push ⟨joinPath (joinPath path "global_info") "status", "ThreadLocalRef static compiler query is unresolved"⟩
      if (info.getObjValAs? Bool "is_static").toOption != some true then
        issues := issues.push ⟨joinPath (joinPath path "global_info") "is_static", "ThreadLocalRef DefId is not confirmed as a static"⟩
      if (info.getObjValAs? Bool "thread_local").toOption != some true then
        issues := issues.push ⟨joinPath (joinPath path "global_info") "thread_local", "ThreadLocalRef DefId is not confirmed as thread-local"⟩
      foreign := (info.getObjValAs? Bool "is_foreign_item").toOption.getD false
      if (info.getObjValAs? Bool "is_foreign_item").toOption.isNone then
        issues := issues.push ⟨joinPath (joinPath path "global_info") "is_foreign_item", "ThreadLocalRef static query lacks its foreign-item predicate"⟩
    let initializer := (value.getObjVal? "initializer").toOption
    match initializer with
    | none => issues := issues.push ⟨joinPath path "initializer", "supported ThreadLocalRef is missing exact initializer query evidence"⟩
    | some initializer =>
      let initializerPath := joinPath path "initializer"
      if (initializer.getObjValAs? String "status").toOption == some "supported" then
        let allocation := (initializer.getObjVal? "allocation").toOption
        match allocation with
        | none => issues := issues.push ⟨joinPath initializerPath "allocation", "supported TLS initializer is missing its allocation image"⟩
        | some allocation =>
          let allocationPath := joinPath initializerPath "allocation"
          match parseAllocationMemory allocation allocationPath with
          | .error reason => issues := issues.push ⟨allocationPath, reason⟩
          | .ok memory =>
            if let some info := info then
              match (info.getObjVal? "size_bytes").bind Json.getNat? with
              | .ok size => if size != memory.sizeBytes then
                  issues := issues.push ⟨joinPath allocationPath "size_bytes", "TLS initializer size disagrees with static compiler query"⟩
              | .error _ => issues := issues.push ⟨joinPath (joinPath path "global_info") "size_bytes", "TLS static query is missing its allocation size"⟩
              match (info.getObjVal? "align_bytes").bind Json.getNat? with
              | .ok align => if align != memory.alignBytes then
                  issues := issues.push ⟨joinPath allocationPath "align_bytes", "TLS initializer alignment disagrees with static compiler query"⟩
              | .error _ => issues := issues.push ⟨joinPath (joinPath path "global_info") "align_bytes", "TLS static query is missing its allocation alignment"⟩
      else if foreign && (initializer.getObjValAs? String "status").toOption != some "unsupported" then
        issues := issues.push ⟨joinPath initializerPath "status", "foreign TLS initializer must remain an explicit unsupported query"⟩
  return issues

private def queryDependencyRole (path : String) : QueryDependencyRole :=
  if exactTypeQueryStatus path || exactDropGlueStatus path || exactInstanceCatalogPath path then .runtimeTypeQuery
  else if exactLibcTypeLayoutStatus path then .runtimeTypeQuery
  else if exactCompilerNamedTypeStatus path then .runtimeTypeQuery
  else if exactCatalogStatus path "compiler_named_constants" ".query.status" ||
      exactCatalogStatus path "compiler_named_constants" ".query.evaluation.status" ||
      exactCatalogStatus path "compiler_named_shim_abis" ".recipe.query.status" ||
      exactCatalogStatus path "compiler_named_shim_abis" ".recipe.query.abi_query.status" ||
      path == "$.compiler_runtime_queries.foreign_symbols.extern_statics.status" ||
      path == "$.compiler_runtime_queries.foreign_symbols.exported_candidates.status" then
    .foreignShim
  else if exactCatalogStatus path "compiler_named_statics" ".query.status" then .namedPathStatic
  else if exactCatalogStatus path "compiler_function_facts.helper_signatures" ".abi_query.status" then .callHelper
  -- Function type normalization and FnPtr ABI queries are catalogued for all
  -- exported types, then demanded only by the exact MIR call operation. The
  -- provider retains each failed query and reports it from the call hook.
  else if exactCatalogStatus path "compiler_function_facts.types" ".signature_query.status" ||
      exactCatalogStatus path "compiler_function_facts.pointer_abis" ".abi_query.status" then
    .runtimeCallMetadata
  -- Extern-static declaration and selected-export queries are materialized
  -- from the allocation graph, but their errors belong to exact symbol or
  -- DefId lookup at runtime, not to unrelated MIR paths. `compiler_fact`
  -- wraps the extern-static table in a `value` field; keep that envelope in
  -- each exact indexed path.
  else if exactCatalogStatus path "compiler_runtime_queries.foreign_symbols.extern_statics.value.declarations" ".status" ||
      exactCatalogStatus path "compiler_runtime_queries.foreign_symbols.extern_statics.value.selected_exported" ".status" ||
      exactCatalogStatus path "compiler_runtime_queries.foreign_symbols.extern_statics.value.selected_exported" ".declaration.status" ||
      exactCatalogStatus path "compiler_runtime_queries.foreign_symbols.extern_statics.value.selected_exported" ".allocation.status" then
    .foreignShim
  else if exactCatalogStatus path "compiler_cast_queries" ".status" then .runtimeCast
  -- These exact compiler call-fact queries are checked by their source-owned
  -- providers when an operation requests them; an unavailable optional row
  -- does not make an unrelated selected MIR body malformed.
  else if exactRuntimeInstanceFactStatus path then .runtimeCallMetadata
  -- Candidate virtual resolutions are a cross-product over compiler vtable
  -- pairs. A failed nonselected row is retained as source evidence; the exact
  -- receiver/type/args lookup rejects it if execution actually demands it.
  else if exactVirtualResolutionStatus path then .runtimeVirtual
  else if exactCatalogStatus path "compiler_type_name_constants" ".status" ||
      exactCatalogStatus path "compiler_caller_location_constants" ".status" then .intrinsicValue
  -- alloc_addresses/mod.rs:167–174 demands this only when constructing a
  -- native compiler-function closure; its provider checks signature_query.status.
  else if exactCatalogStatus path "compiler_native_signature_queries" ".signature_query.status" then
    .nativeCallbackSignature
  else if path == "$.compiler_main_queries.link_sections.status" then .programStartup
  else .structural

private def obligationQueryRole (path : String) : QueryDependencyRole :=
  let canonical := if path.startsWith "$." then path else "$." ++ path
  let direct := queryDependencyRole canonical
  if direct != .structural then direct
  else queryDependencyRole (canonical ++ ".status")

private def pathCanReach (wanted path : String) : Bool :=
  wanted == path || wanted.startsWith (path ++ ".") || wanted.startsWith (path ++ "[")

private def jsonAtPathSegment (j : Json) (segment : String) : Option Json := Id.run do
  match segment.splitOn "[" with
  | [key] => return (j.getObjVal? key).toOption
  | [key, suffix] =>
    let pieces := suffix.splitOn "]"
    let [indexText, ""] := pieces | return none
    let .ok index := decimalNat indexText segment | return none
    let some arrayJson := (j.getObjVal? key).toOption | return none
    let some values := arrayJson.getArr?.toOption | return none
    return values[index]?
  | _ => return none

def jsonAtPath (j : Json) (path : String) : Option Json := Id.run do
  unless path.startsWith "$." do return none
  let segments := (path.drop 2).toString.splitOn "."
  let mut current := some j
  for segment in segments do
    current := current.bind (fun value => jsonAtPathSegment value segment)
  return current

private def jsonTypeId? (j : Json) : Option Nat :=
  (j.getObjVal? "type_id").toOption.bind (fun value => value.getNat?.toOption)

private def dynamicPredicateArray? (j : Json) (typeId : Nat) : Option (Array Json) := Id.run do
  let some types := (((j.getObjVal? "types").bind Json.getArr?).toOption) | return none
  let matching := types.filter fun ty =>
    ((ty.getObjValAs? Nat "type_id").toOption == some typeId)
  unless matching.size == 1 do return none
  let some ty := matching[0]? | return none
  let some shape := (ty.getObjVal? "shape").toOption | return none
  unless ((shape.getObjValAs? String "kind").toOption == some "dynamic_trait_object") do return none
  return ((shape.getObjVal? "predicates").bind Json.getArr?).toOption

private def compilerBuiltinDerefType? (j : Json) (typeId : Nat) : Option Nat := Id.run do
  let some types := (((j.getObjVal? "types").bind Json.getArr?).toOption) | return none
  let matching := types.filter fun ty =>
    ((ty.getObjValAs? Nat "type_id").toOption == some typeId)
  unless matching.size == 1 do return none
  let some ty := matching[0]? | return none
  let some facts := (ty.getObjVal? "compiler_facts").toOption | return none
  let some queries := (facts.getObjVal? "type_queries").toOption | return none
  let some query := (queries.getObjVal? "builtin_deref_explicit").toOption | return none
  unless ((query.getObjValAs? String "status").toOption == some "supported") do return none
  let some value := (query.getObjVal? "value").toOption | return none
  return jsonTypeId? value

private def exactLockstepTails? (j : Json) (source target : Nat) : Option Json := Id.run do
  let some rows := (((j.getObjVal? "compiler_cast_queries").bind Json.getArr?).toOption) | return none
  let matching := rows.filter fun row =>
    ((row.getObjValAs? String "query_kind").toOption == some "lockstep_tails") &&
    ((row.getObjValAs? String "typing_env").toOption == some "fully_monomorphized") &&
    ((row.getObjValAs? String "status").toOption == some "supported") &&
    ((row.getObjVal? "input_source").toOption.bind jsonTypeId? == some source) &&
    ((row.getObjVal? "input_target").toOption.bind jsonTypeId? == some target)
  unless matching.size == 1 do return none
  return matching[0]?

private def castOperandTypeId? (node : Json) : Option Nat := Id.run do
  let some operand := (node.getObjVal? "operand").toOption | return none
  let some operandKind := ((operand.getObjVal? "kind").bind Json.getStr?).toOption | return none
  if operandKind == "Copy" || operandKind == "Move" then
    let some place := (operand.getObjVal? "place").toOption | return none
    let some ty := (place.getObjVal? "type").toOption | return none
    return jsonTypeId? ty
  else if operandKind == "Constant" then
    let some constant := (operand.getObjVal? "constant").toOption | return none
    let some ty := (constant.getObjVal? "type").toOption | return none
    return jsonTypeId? ty
  else return none

/-- The exporter may retain its salt-zero CTFE vtable probe as diagnostic
evidence, but it is not a runtime allocation identity. Only the exact probe
leaf attached to a supported concrete Unsize Cast and backed by a supported
exact-pair query is demand-local. The enclosing Cast must itself be supported;
all other statuses and descendants remain structural blockers. -/
def exactVtableProbeDiagnostic (j : Json) (path : String) : Bool := Id.run do
  let suffix := ".vtable_probe.status"
  unless path.endsWith suffix do return false
  let castPath := (path.dropEnd suffix.length).toString
  let some node := jsonAtPath j castPath | return false
  unless ((node.getObjValAs? String "status").toOption == some "supported") do return false
  unless ((node.getObjValAs? String "kind").toOption == some "Cast") do return false
  let some castKind := (node.getObjVal? "cast_kind").toOption | return false
  unless ((castKind.getObjValAs? String "status").toOption == some "supported") &&
      ((castKind.getObjValAs? String "kind").toOption == some "PointerCoercion") do return false
  let some coercion := (castKind.getObjVal? "coercion").toOption | return false
  unless ((coercion.getObjValAs? String "kind").toOption == some "Unsize") do return false
  let some sourceType := (node.getObjVal? "target_type").toOption | return false
  let some sourceTypeId := jsonTypeId? sourceType | return false
  unless castOperandTypeId? node |>.isSome do return false
  let some operandTypeId := castOperandTypeId? node | return false
  let some queryRef := (node.getObjVal? "vtable_query").toOption | return false
  unless ((queryRef.getObjValAs? String "status").toOption == some "supported") do return false
  let some queryId := ((queryRef.getObjVal? "query_id").bind Json.getNat?).toOption | return false
  let some querySource := (queryRef.getObjVal? "source_type").toOption | return false
  let some queryTarget := (queryRef.getObjVal? "target_type").toOption | return false
  unless jsonTypeId? querySource == some operandTypeId && jsonTypeId? queryTarget == some sourceTypeId do return false
  let some sourcePointee := (queryRef.getObjVal? "source_pointee_type").toOption | return false
  let some targetPointee := (queryRef.getObjVal? "target_pointee_type").toOption | return false
  let some sourcePointeeId := jsonTypeId? sourcePointee | return false
  let some targetPointeeId := jsonTypeId? targetPointee | return false
  unless compilerBuiltinDerefType? j operandTypeId == some sourcePointeeId &&
      compilerBuiltinDerefType? j sourceTypeId == some targetPointeeId do return false
  let some fullLockstep := exactLockstepTails? j operandTypeId sourceTypeId | return false
  let some fullLockstepValue := (fullLockstep.getObjVal? "value").toOption | return false
  unless ((fullLockstepValue.getObjVal? "source_tail").toOption.bind jsonTypeId? == some operandTypeId) &&
      ((fullLockstepValue.getObjVal? "target_tail").toOption.bind jsonTypeId? == some sourceTypeId) do return false
  let some sourceTail := (queryRef.getObjVal? "source_tail_type").toOption | return false
  let some targetTail := (queryRef.getObjVal? "target_tail_type").toOption | return false
  let some sourceTailId := jsonTypeId? sourceTail | return false
  let some targetTailId := jsonTypeId? targetTail | return false
  let some inputType := (queryRef.getObjVal? "input_type").toOption | return false
  let some inputTypeId := jsonTypeId? inputType | return false
  unless inputTypeId == sourceTailId do return false
  let some queryPredicates := ((queryRef.getObjVal? "input_predicates").bind Json.getArr?).toOption | return false
  let some targetPredicates := dynamicPredicateArray? j targetTailId | return false
  unless targetPredicates == queryPredicates do return false
  let some lockstep := exactLockstepTails? j sourcePointeeId targetPointeeId | return false
  let some lockstepValue := (lockstep.getObjVal? "value").toOption | return false
  unless ((lockstepValue.getObjVal? "source_tail").toOption.bind jsonTypeId? == some sourceTailId) &&
      ((lockstepValue.getObjVal? "target_tail").toOption.bind jsonTypeId? == some targetTailId) do return false
  let some rows := (((j.getObjVal? "compiler_vtable_queries").bind Json.getArr?).toOption) | return false
  let matching := rows.filter fun row =>
    ((row.getObjValAs? Nat "query_id").toOption == some queryId)
  unless matching.size == 1 do return false
  let some row := matching[0]? | return false
  unless ((row.getObjValAs? String "status").toOption == some "supported") do return false
  unless ((row.getObjVal? "input_type").toOption.bind jsonTypeId? == some inputTypeId) do return false
  unless jsonTypeId? ((row.getObjVal? "output_type").toOption.getD .null) |>.isSome do return false
  let some rowInputPredicates := ((row.getObjVal? "input_predicates").bind Json.getArr?).toOption | return false
  unless rowInputPredicates == queryPredicates do return false
  unless ((row.getObjVal? "output_predicates").bind Json.getArr?).isOk do return false
  unless ((row.getObjValAs? Bool "output_type_monomorphic_enough").toOption == some true) &&
      ((row.getObjValAs? Bool "output_predicates_monomorphic_enough").toOption == some true) do return false
  let some probe := (node.getObjVal? "vtable_probe").toOption | return false
  unless ((probe.getObjValAs? String "status").toOption == some "incomplete") &&
      ((probe.getObjValAs? String "kind").toOption == some "symbolic_vtable_allocation") &&
      (((probe.getObjValAs? String "salt_policy").toOption.getD "").startsWith
        "exporter uses CTFE_ALLOC_SALT; Miri runtime allocation salts may be randomized") do return false
  unless (node.getObjVal? "vtable_allocation").toOption == some .null do return false
  unless (match probe.getObjVal? "allocation" with | .error _ => true | .ok _ => false) &&
      (match probe.getObjVal? "allocation_id" with | .error _ => true | .ok _ => false) do return false
  return true

/-- A dynamic-to-dynamic Unsize is represented by the runtime source-vtable
operation. Bind its descriptor to the Cast's complete types, both exact
lockstep queries, and the compiler's fully-monomorphized supertrait-slot row.
This validates evidence identity only; the runtime still obtains the table
from the actual source operand. -/
private def castUnsizingPointeeType? (j : Json) (typeId : Nat) : Option Nat := Id.run do
  let some types := (((j.getObjVal? "types").bind Json.getArr?).toOption) | return none
  let matching := types.filter fun ty => (ty.getObjValAs? Nat "type_id").toOption == some typeId
  unless matching.size == 1 do return none
  let some ty := matching[0]? | return none
  let some shape := (ty.getObjVal? "shape").toOption | return none
  let some kind := (shape.getObjValAs? String "kind").toOption | return none
  if kind == "reference" || kind == "raw_pointer" then
    return (shape.getObjVal? "pointee").toOption.bind jsonTypeId?
  else
    return some typeId

private def exactDynamicVtableUpcast? (j node descriptor : Json) : Bool := Id.run do
  unless ((node.getObjValAs? String "status").toOption == some "supported") &&
      ((node.getObjValAs? String "kind").toOption == some "Cast") do return false
  let some castKind := (node.getObjVal? "cast_kind").toOption | return false
  unless ((castKind.getObjValAs? String "status").toOption == some "supported") &&
      ((castKind.getObjValAs? String "kind").toOption == some "PointerCoercion") do return false
  let some coercion := (castKind.getObjVal? "coercion").toOption | return false
  unless (coercion.getObjValAs? String "kind").toOption == some "Unsize" do return false
  unless ((descriptor.getObjValAs? String "status").toOption == some "supported") &&
      ((descriptor.getObjValAs? String "kind").toOption == some "dynamic_vtable_upcast") do return false
  let some sourceType := (descriptor.getObjVal? "source_type").toOption | return false
  let some sourceTypeId := jsonTypeId? sourceType | return false
  let some targetType := (descriptor.getObjVal? "target_type").toOption | return false
  let some targetTypeId := jsonTypeId? targetType | return false
  unless castOperandTypeId? node == some sourceTypeId do return false
  unless ((node.getObjVal? "target_type").toOption.bind jsonTypeId?) == some targetTypeId do return false

  let some sourcePointee := (descriptor.getObjVal? "source_pointee_type").toOption | return false
  let some sourcePointeeId := jsonTypeId? sourcePointee | return false
  let some targetPointee := (descriptor.getObjVal? "target_pointee_type").toOption | return false
  let some targetPointeeId := jsonTypeId? targetPointee | return false
  unless castUnsizingPointeeType? j sourceTypeId == some sourcePointeeId &&
      castUnsizingPointeeType? j targetTypeId == some targetPointeeId do return false

  let some fullLockstep := exactLockstepTails? j sourceTypeId targetTypeId | return false
  let some fullValue := (fullLockstep.getObjVal? "value").toOption | return false
  let some fullSourceTail := ((fullValue.getObjVal? "source_tail").toOption.bind jsonTypeId?) | return false
  let some fullTargetTail := ((fullValue.getObjVal? "target_tail").toOption.bind jsonTypeId?) | return false
  unless fullSourceTail == sourceTypeId && fullTargetTail == targetTypeId do return false

  let some sourcePointeeLockstep := exactLockstepTails? j sourcePointeeId targetPointeeId | return false
  let some pointeeValue := (sourcePointeeLockstep.getObjVal? "value").toOption | return false
  let some sourceTail := (descriptor.getObjVal? "source_tail_type").toOption | return false
  let some sourceTailId := jsonTypeId? sourceTail | return false
  let some targetTail := (descriptor.getObjVal? "target_tail_type").toOption | return false
  let some targetTailId := jsonTypeId? targetTail | return false
  unless ((pointeeValue.getObjVal? "source_tail").toOption.bind jsonTypeId?) == some sourceTailId &&
      ((pointeeValue.getObjVal? "target_tail").toOption.bind jsonTypeId?) == some targetTailId do return false
  unless (dynamicPredicateArray? j sourceTailId).isSome &&
      (dynamicPredicateArray? j targetTailId).isSome do return false

  unless (descriptor.getObjValAs? String "runtime_vtable").toOption ==
      some "source_operand_metadata" do return false
  let some embeddedQuery := (descriptor.getObjVal? "supertrait_slot_query").toOption | return false
  unless ((embeddedQuery.getObjValAs? String "status").toOption == some "supported") &&
      ((embeddedQuery.getObjValAs? String "query_kind").toOption == some "supertrait_slot") &&
      ((embeddedQuery.getObjValAs? String "typing_env").toOption == some "fully_monomorphized") &&
      ((embeddedQuery.getObjVal? "input_source").toOption.bind jsonTypeId? == some sourceTailId) &&
      ((embeddedQuery.getObjVal? "input_target").toOption.bind jsonTypeId? == some targetTailId) do return false
  let some rows := (((j.getObjVal? "compiler_cast_queries").bind Json.getArr?).toOption) | return false
  let matching := rows.filter fun row =>
    ((row.getObjValAs? String "query_kind").toOption == some "supertrait_slot") &&
    ((row.getObjValAs? String "typing_env").toOption == some "fully_monomorphized") &&
    ((row.getObjValAs? String "status").toOption == some "supported") &&
    ((row.getObjVal? "input_source").toOption.bind jsonTypeId? == some sourceTailId) &&
    ((row.getObjVal? "input_target").toOption.bind jsonTypeId? == some targetTailId)
  unless matching.size == 1 do return false
  let some row := matching[0]? | return false
  unless (match row.getObjVal? "value" with
    | .ok .null => true
    | .ok value => (value.getNat?).isOk
    | .error _ => false) do return false
  return true

private partial def malformedDynamicVtableUpcastAux (root : Json) (node : JsonTraversalCache.Node) (path : String)
    (visited : Std.HashSet JsonTraversalCache.Key) : Option String × Std.HashSet JsonTraversalCache.Key := Id.run do
  let current := node.value
  let memoKey := node.key
  match current with
  | .obj _ | .arr _ => pure ()
  | _ => return (none, visited)
  if visited.contains memoKey then return (none, visited)
  let mut visited := visited.insert memoKey
  match current with
  | .obj fields =>
    if (current.getObjValAs? String "kind").toOption == some "Cast" then
      if let some descriptor := (current.getObjVal? "vtable_allocation").toOption then
        if (descriptor.getObjValAs? String "kind").toOption == some "dynamic_vtable_upcast" &&
            (descriptor.getObjValAs? String "status").toOption == some "supported" &&
            !exactDynamicVtableUpcast? root current descriptor then
          return (some (joinPath path "vtable_allocation"), visited)
    for ((key, value), childIndex) in fields.toList.zipIdx do
      let (badPath?, nextVisited) := malformedDynamicVtableUpcastAux root (node.child childIndex value) (joinPath path key) visited
      visited := nextVisited
      if let some badPath := badPath? then return (some badPath, visited)
  | .arr values =>
    for (value, childIndex) in values.toList.zipIdx do
      let (badPath?, nextVisited) := malformedDynamicVtableUpcastAux root (node.child childIndex value) s!"{path}[{childIndex}]" visited
      visited := nextVisited
      if let some badPath := badPath? then return (some badPath, visited)
  | _ => pure ()
  return (none, visited)

private def malformedDynamicVtableUpcast? (node : JsonTraversalCache.Node) : Option String :=
  (malformedDynamicVtableUpcastAux node.value node "$" {}).1

private partial def hasFailedStatusAt (j : Json) (wanted path : String) : Bool := Id.run do
  match j with
  | .obj fields =>
    if (j.getObjValAs? String "status").toOption == some "debug_payload" then return false
    if path == wanted then
      if let some status := (j.getObjValAs? String "status").toOption then
        if status != "supported" then return true
    for (key, value) in fields.toList do
      let child := joinPath path key
      if pathCanReach wanted child && hasFailedStatusAt value wanted child then return true
  | .arr values =>
    for (value, index) in values.toList.zipIdx do
      let child := s!"{path}[{index}]"
      if pathCanReach wanted child && hasFailedStatusAt value wanted child then return true
  | _ => pure ()
  return false

/-- Copied catalog diagnostics inherit only their exact original query role.
The original obligations remain present; runtime providers still reject failed
queries when the corresponding source operation requests them. -/
private def retainedQueryDiagnosticRole (j : Json) (path : String) : QueryDependencyRole := Id.run do
  let pathPrefix := "$.selected_scope.retained_catalog_obligations["
  let suffix := "].status"
  unless path.startsWith pathPrefix && path.endsWith suffix do return .structural
  let indexText := ((path.drop pathPrefix.length).dropEnd suffix.length).toString
  let .ok index := decimalNat indexText path | return .structural
  unless toString index == indexText do return .structural
  let some records := (((j.getObjVal? "selected_scope").bind fun scope =>
      (scope.getObjVal? "retained_catalog_obligations").bind Json.getArr?).toOption)
    | return .structural
  let some record := records[index]? | return .structural
  let some sourcePath := ((record.getObjVal? "path").bind Json.getStr?).toOption
    | return .structural
  unless hasFailedStatusAt j ("$." ++ sourcePath) "$" do return .structural
  if exactVtableProbeDiagnostic j ("$." ++ sourcePath ++ ".status") then return .runtimeCast
  return queryDependencyRole ("$." ++ sourcePath ++ ".status")

/-- Return exactly the selected-scope obligations that the readiness gate
blocks on. Keep diagnostics and the execution decision on this single
predicate so reports cannot drift from the fail-closed gate. -/
private def selectedScopeBlockingObligations (j : Json) (obligations : Array Obligation)
    (requiredLayoutPaths : List String) (requiredInstancePaths : Array String) : Array Obligation :=
  obligations.filter fun issue =>
    (!globalCompletenessPath issue.path && !exactVtableProbeDiagnostic j issue.path &&
      obligationQueryRole issue.path == .structural &&
      retainedQueryDiagnosticRole j issue.path == .structural
      || issue.path == "$.selected_scope.kind" || issue.path == "$.selected_scope.status" ||
      issue.path == "$.selected_scope.semantics" || issue.path.startsWith "$.selected_scope.roots[" ||
      requiredLayoutPaths.contains issue.path ||
      requiredInstancePaths.contains issue.path)

private inductive ParsedDocument where
  | full (result : DecodeResult)
  | runtime (result : RuntimeDecodeResult)

private def parseTypeArray (values : Array Json) (memo : DecodeMemo) : Except String (Array TypeNode) := do
  let mut result := #[]
  let mut index := 0
  for value in values do
    result := result.push (← parseTypeNode value s!"$.types[{index}]" memo)
    index := index + 1
  pure result

private def parseAllocationArray (values : Array Json) : Except String (Array AllocationNode) := do
  let mut result := #[]
  let mut index := 0
  for value in values do
    result := result.push (← parseAllocation value s!"$.allocations[{index}]")
    index := index + 1
  pure result

private def parseInstanceArray (values : Array Json) : Except String (Array InstanceNode) := do
  let mut result := #[]
  let mut index := 0
  for value in values do
    result := result.push (← parseInstance value s!"$.instances[{index}]")
    index := index + 1
  pure result

private def parseBodyArray (values : Array Json) (memo : DecodeMemo) : Except String (Array Body) := do
  let mut result := #[]
  let mut index := 0
  for value in values do
    let fallback := match optionalField value "def_path" with
      | some (.str name) => name
      | _ => s!"body[{index}]"
    result := result.push (← parseBody value s!"$.bodies[{index}]" fallback memo)
    index := index + 1
  pure result

private def parseDocument (input : Json) (runtimeOnly : Bool := false)
    (profile : Options := {}) (cachedTraversal : Bool := true) : Except String ParsedDocument := do
  let (resolved,traversal) ← profileit "decoder.shared_payload_resolution" profile fun _ =>
    JsonTraversalCache.resolve input cachedTraversal profile
  let j := resolved.root
  let memo := profileit "decoder.shared_decode_memo" profile fun _ => sharedDecodeMemo resolved.nodes
  if (← fieldString j "schema" "$") != expectedSchema then
    throw s!"$.schema: expected `{expectedSchema}`"
  if (← fieldNat j "schema_version" "$") != expectedSchemaVersion then
    throw s!"$.schema_version: unsupported schema version"
  if let some path := profileit "decoder.dynamic_vtable_scan" profile fun _ =>
      malformedDynamicVtableUpcast? traversal then
    throw s!"{path}: supported dynamic vtable upcast lacks matching compiler cast evidence"
  let producerJson ← field j "producer" "$"
  let producer : Producer := {
    miriCommit := ← fieldString producerJson "miri_commit" "$.producer"
    rustcCommit := ← fieldString producerJson "rustc_commit" "$.producer"
    rustcVersion := ← fieldString producerJson "rustc_version" "$.producer"
    targetTriple := ← fieldString producerJson "target_triple" "$.producer"
  }
  if producer.miriCommit != expectedMiriCommit then throw "$.producer.miri_commit: input is from the wrong pinned Miri revision"
  if producer.rustcCommit != expectedRustcCommit then throw "$.producer.rustc_commit: input is from the wrong pinned rustc revision"
  let completeness ← field j "completeness" "$"
  let completeStatus ← fieldString completeness "status" "$.completeness"
  if !(← fieldBool completeness "unsupported_payloads_are_explicit" "$.completeness") then
    throw "$.completeness.unsupported_payloads_are_explicit: must be true"
  let typesJson ← arrayField j "types" "$"
  if typesJson.isEmpty then throw "$.types: input has no type graph; refusing an empty import"
  let types ← profileit "decoder.types" profile fun _ => parseTypeArray typesJson memo
  let allocationsJson ← arrayField j "allocations" "$"
  let allocations ← profileit "decoder.allocations" profile fun _ => parseAllocationArray allocationsJson
  let compilerAllocIdWorld ← profileit "decoder.compiler_alloc_id_world" profile fun _ => do
    match optionalJson j "compiler_alloc_id_world" with
    | none => pure none
    | some value => pure (some (← parseCompilerAllocIdWorld value allocations))
  let instancesJson ← arrayField j "instances" "$"
  let instances ← profileit "decoder.instances" profile fun _ => parseInstanceArray instancesJson
  let selectedScope ← match optionalJson j "selected_scope" with
    | none => pure none
    | some value => pure (some (← parseSelectedScope value "$.selected_scope"))
  let functionAbis ← profileit "decoder.function_abis" profile fun _ => collectFunctionAbis traversal "$" memo
  let compilerAbiLayoutSchema ← optionalString j "compiler_abi_layout_schema" "$"
  if let some schema := compilerAbiLayoutSchema then
    if schema != expectedCompilerAbiLayoutSchema then
      throw s!"$.compiler_abi_layout_schema: unsupported schema `{schema}`"
    for (abi, abiIndex) in functionAbis.toList.zipIdx do
      for (argument, abiArgumentIndex) in (abi.arguments.push abi.returnValue).toList.zipIdx do
        if argument.layout.isNone then
          throw s!"$.compiler_abi_layout_schema: ABI record {abiIndex} argument {abiArgumentIndex} lacks its physical layout"
  let bodiesJson ← arrayField j "bodies" "$"
  if bodiesJson.isEmpty then throw "$.bodies: input has no MIR bodies; refusing an empty import"
  let bodies ← profileit "decoder.bodies" profile fun _ => parseBodyArray bodiesJson memo
  let typeIds := jsonToNatArray types (·.id)
  let allocationIds := jsonToNatArray allocations (·.id)
  let instanceIds := jsonToNatArray instances (·.id)
  profileit "decoder.validate_dense_type_ids" profile fun _ => validateDense typeIds "type IDs"
  profileit "decoder.validate_dense_allocation_ids" profile fun _ => validateDense allocationIds "allocation IDs"
  profileit "decoder.validate_dense_instance_ids" profile fun _ => validateDense instanceIds "instance IDs"
  profileit "decoder.validate_all_bodies" profile fun _ => validateAllBodies traversal "$"
  profileit "decoder.validate_references" profile fun _ =>
    validateReferences traversal "$" types.size allocations.size instances.size
  let (typedTree?, valueIssues) ← if runtimeOnly then
      let decoded ← profileit "decoder.runtime_value" profile fun _ =>
        decodeRuntimeValue j "$" .any .none memo
      pure (none, flattenRuntimeObligations decoded.obligations)
    else
      let typedTree ← decodeValue j "$" .any .none memo
      pure (some typedTree, valueObligations typedTree "$")
  let mut obligations := valueIssues
  obligations := obligations ++ profileit "decoder.extra_semantic_obligations" profile fun _ =>
    extraSemanticObligations j types allocations instances functionAbis bodies
  let requiredDependencies := profileit "decoder.required_dependencies" profile fun _ =>
    requiredStructuralDependencies j compilerAllocIdWorld.isSome
  obligations := profileit "decoder.prepared_world_readiness" profile fun _ =>
    preparedWorldReadinessObligations obligations compilerAllocIdWorld allocations
      requiredDependencies.allocationIds
  obligations := obligations ++ profileit "decoder.required_instance_obligations" profile fun _ =>
    requiredIdentityOnlyInstanceObligations instances requiredDependencies.instanceIds
  obligations := obligations ++ profileit "decoder.thread_local_obligations" profile fun _ =>
    threadLocalShapeObligations requiredDependencies.threadLocalRefs
  match selectedScope with
  | some scope => obligations := obligations ++ profileit "decoder.selected_scope_obligations" profile fun _ =>
      selectedScopeObligations scope bodies instances
  | none => pure ()
  let unresolved ← arrayField completeness "unresolved_obligations" "$.completeness"
  if completeStatus != "complete" then
    let message := if completeStatus == "incomplete" then
        "exporter marked the graph incomplete; this import cannot form executable input"
      else s!"unrecognized completeness status `{completeStatus}`"
    obligations := obligations.push ⟨"$.completeness.status", message⟩
  for (message, obligationIndex) in unresolved.toList.zipIdx do
    match message.getStr? with
    | .ok text => obligations := obligations.push ⟨s!"$.completeness.unresolved_obligations[{obligationIndex}]", text⟩
    | .error _ => throw s!"$.completeness.unresolved_obligations[{obligationIndex}]: expected string"
  let runtimeTargetDataLayout ← match optionalJson j "runtime_target_data_layout" with
    | none => pure none
    | some evidence => pure (some ({
        status := parseStatus (← fieldString evidence "status" "$.runtime_target_data_layout")
        payload := evidence
      } : TargetDataLayoutEvidence))
  let core : ImportDocumentCore := {
    compilerPredicates := ← match optionalField j "compiler_predicate_queries" with
      | none => pure #[]
      | some value => (← value.getArr?).mapM decodeCompilerPredicateEvidence
    compilerAbiLayoutSchema := compilerAbiLayoutSchema
    producer := producer
    runtimeTargetDataLayout := runtimeTargetDataLayout
    completenessStatus := parseStatus completeStatus
    types := types
    allocations := allocations
    compilerAllocIdWorld := compilerAllocIdWorld
    instances := instances
    selectedScope := selectedScope
    functionAbis := functionAbis
    bodies := bodies
    obligations := obligations
    raw := j
    sharedNodes := resolved.nodes
  }
  let requiredLayoutPaths := types.toList.zipIdx.filterMap fun (ty, typeIndex) =>
    if requiredDependencies.typeIds.contains ty.id then some s!"$.types[{typeIndex}].layout.status" else none
  let requiredInstancePaths := instances.toList.zipIdx.foldl (fun paths (instNode, instanceIndex) =>
    if requiredDependencies.instanceIds.contains instNode.id then
      paths ++ #[s!"instances[{instanceIndex}]", s!"$.instances[{instanceIndex}].status"]
    else paths) #[]
  let scopeIsSelected := selectedScope.isSome
  let blockingObligations := if scopeIsSelected then
      selectedScopeBlockingObligations j obligations requiredLayoutPaths requiredInstancePaths
    else obligations
  let scopeIssuesRemain := !blockingObligations.isEmpty
  let ready :=
    if scopeIsSelected then !scopeIssuesRemain
    else completeStatus == "complete" && obligations.isEmpty
  match typedTree? with
  | some typedTree =>
    let doc := core.withTypedTree typedTree
    let executionInput := if ready then some ⟨doc⟩ else none
    return .full ⟨doc, executionInput, blockingObligations⟩
  | none =>
    let executionInput := if ready then some ⟨core⟩ else none
    return .runtime ⟨core, executionInput, blockingObligations⟩

def decodeJson (text : String) : Except String DecodeResult := do
  let json ← Json.parse text
  match ← parseDocument json with
  | .full result => pure result
  | .runtime _ => throw "internal decoder mode mismatch"

def decodeFile (path : System.FilePath) : IO (Except String DecodeResult) := do
  try
    let text ← IO.FS.readFile path
    pure (decodeJson text)
  catch error => pure (.error s!"could not read {path}: {error}")

/-- Runtime decoder with optional Lean profiler options. Profiling wrappers are
kernel identity functions; with profiling disabled this preserves the ordinary
decoder result and diagnostic order. -/
def decodeRuntimeJsonProfiled (text : String) (profile : Options) : Except String RuntimeDecodeResult := do
  let json ← profileit "decoder.json_parse" profile fun _ => Json.parse text
  match ← profileit "decoder.document" profile fun _ => parseDocument json true profile with
  | .runtime result => pure result
  | .full _ => throw "internal decoder mode mismatch"

/-- Regression oracle: identical validation with the structural-hash memo off.
This is not a relaxed decoder and retains the full original error ordering. -/
def decodeRuntimeJsonReference (text : String) : Except String RuntimeDecodeResult := do
  let json ← Json.parse text
  match ← parseDocument json true {} false with
  | .runtime result => pure result
  | .full _ => throw "internal decoder mode mismatch"

def decodeJsonReference (text : String) : Except String DecodeResult := do
  let json ← Json.parse text
  match ← parseDocument json false {} false with
  | .full result => pure result
  | .runtime _ => throw "internal decoder mode mismatch"

/-- Runtime-only entry point, preserving validation and diagnostic precedence
without retaining the full typed projection. -/
def decodeRuntimeJson (text : String) : Except String RuntimeDecodeResult :=
  decodeRuntimeJsonProfiled text {}

def decodeRuntimeFile (path : System.FilePath) : IO (Except String RuntimeDecodeResult) := do
  try
    let text ← IO.FS.readFile path
    pure (decodeRuntimeJson text)
  catch error => pure (.error s!"could not read {path}: {error}")

/-- Typed metadata entrypoints for compiler-query adapters. -/
def decodeAllocationMemoryEvidence (j : Json) : Except String AllocationMemory :=
  parseAllocationMemory j "$allocation"

def decodeCompilerValue (j : Json) : Except String TypedValue :=
  decodeValue j "$compiler_value"

end Miri.Input
