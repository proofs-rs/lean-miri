import Miri.Input.Model.Types
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

def field (j : Json) (key path : String) : Except String Json := do
  j.getObjVal? key |>.mapError fun e => s!"{path}: missing/invalid field `{key}` ({e})"

def fieldNat (j : Json) (key path : String) : Except String Nat := do
  let v ← field j key path
  v.getNat? |>.mapError fun e => s!"{joinPath path key}: expected unsigned integer ({e})"

def fieldString (j : Json) (key path : String) : Except String String := do
  let v ← field j key path
  v.getStr? |>.mapError fun e => s!"{joinPath path key}: expected string ({e})"

def fieldBool (j : Json) (key path : String) : Except String Bool := do
  let v ← field j key path
  v.getBool? |>.mapError fun e => s!"{joinPath path key}: expected boolean ({e})"

def arrayField (j : Json) (key path : String) : Except String (Array Json) := do
  let v ← field j key path
  v.getArr? |>.mapError fun e => s!"{joinPath path key}: expected array ({e})"

def optionalNatField (j : Json) (key path : String) : Except String (Option Nat) := do
  let v ← field j key path
  if v == .null then pure none else
    (v.getNat?).map some |>.mapError fun e => s!"{joinPath path key}: expected unsigned integer or null ({e})"

def optionalField (j : Json) (key : String) : Option Json :=
  (j.getObjVal? key).toOption

def optionalString (j : Json) (key path : String) : Except String (Option String) := do
  match optionalField j key with
  | none | some .null => pure none
  | some value => (value.getStr?).map some |>.mapError fun e => s!"{joinPath path key}: expected string ({e})"

def objectFields (j : Json) : Except String (Array (String × Json)) := do
  match j with
  | .obj fields => pure fields.toList.toArray
  | _ => throw "expected object"

def statusOf? (j : Json) : Option String :=
  match optionalField j "status" with
  | none => none
  | some value => match value.getStr? with | .ok text => some text | .error _ => none


def sourceDebugString (j : Json) (key path : String) : Except String String := do
  let value ← field j key path
  match value with
  | .str text => pure text
  | .obj _ =>
    if statusOf? value != some "debug_payload" then
      throw s!"{joinPath path key}: expected string or diagnostic debug payload"
    fieldString value "rustc_debug" (joinPath path key)
  | _ => throw s!"{joinPath path key}: expected string or diagnostic debug payload"

def parseSourcePosition (j : Json) (path : String) : Except String SourcePosition := do
  return {
    line := ← fieldNat j "line" path
    column := ← fieldNat j "column" path
  }

def parseSourceSpan (j : Json) (path : String) : Except String SourceSpanData := do
  let start ← parseSourcePosition (← field j "start" path) (joinPath path "start")
  let endPos ← parseSourcePosition (← field j "end" path) (joinPath path "end")
  return {
    isDummy := ← fieldBool j "is_dummy" path
    originalPayload := j.compress
    lo := ← fieldNat j "lo" path
    hi := ← fieldNat j "hi" path
    start := start
    «end» := endPos
    context := ← sourceDebugString j "ctxt" path
    file := ← sourceDebugString j "file" path
  }

def parseSourceInfo (j : Json) (path : String) : Except String SourceInfo := do
  return {
    spanId := ← fieldNat j "span" path
    scope := ← fieldNat j "scope" path
  }

def hasField (j : Json) (key : String) : Bool := (j.getObjVal? key).isOk

def statementVariant (tag : String) : Except String StatementVariant :=
  match tag with
  | "Assign" => pure (.assign)
  | "FakeRead" => pure (.fakeRead)
  | "SetDiscriminant" => pure (.setDiscriminant)
  | "StorageLive" => pure (.storageLive)
  | "StorageDead" => pure (.storageDead)
  | "PlaceMention" => pure (.placeMention)
  | "AscribeUserType" => pure (.ascribeUserType)
  | "Coverage" => pure (.coverage)
  | "Intrinsic" => pure (.intrinsic)
  | "ConstEvalCounter" => pure (.constEvalCounter)
  | "Nop" => pure (.nop)
  | "BackwardIncompatibleDropHint" => pure (.backwardIncompatibleDropHint)
  | other => throw s!"unrecognized statementVariant tag `{other}`"

def terminatorVariant (tag : String) : Except String TerminatorVariant :=
  match tag with
  | "Goto" => pure (.goto)
  | "SwitchInt" => pure (.switchInt)
  | "UnwindResume" => pure (.unwindResume)
  | "UnwindTerminate" => pure (.unwindTerminate)
  | "Return" => pure (.return)
  | "Unreachable" => pure (.unreachable)
  | "Drop" => pure (.drop)
  | "Call" => pure (.call)
  | "TailCall" => pure (.tailCall)
  | "Assert" => pure (.assert)
  | "Yield" => pure (.yield)
  | "CoroutineDrop" => pure (.coroutineDrop)
  | "FalseEdge" => pure (.falseEdge)
  | "FalseUnwind" => pure (.falseUnwind)
  | "InlineAsm" => pure (.inlineAsm)
  | other => throw s!"unrecognized terminatorVariant tag `{other}`"

def rvalueVariant (tag : String) : Except String RvalueVariant :=
  match tag with
  | "Use" => pure (.use)
  | "Repeat" => pure (.repeat)
  | "Ref" => pure (.ref)
  | "ThreadLocalRef" => pure (.threadLocalRef)
  | "RawPtr" => pure (.rawPtr)
  | "Cast" => pure (.cast)
  | "BinaryOp" => pure (.binaryOp)
  | "UnaryOp" => pure (.unaryOp)
  | "Discriminant" => pure (.discriminant)
  | "Aggregate" => pure (.aggregate)
  | "CopyForDeref" => pure (.copyForDeref)
  | "WrapUnsafeBinder" => pure (.wrapUnsafeBinder)
  | "Reborrow" => pure (.reborrow)
  | other => throw s!"unrecognized rvalueVariant tag `{other}`"

def operandVariant (tag : String) : Except String OperandVariant :=
  match tag with
  | "Copy" => pure (.copy)
  | "Move" => pure (.move)
  | "Constant" => pure (.constant)
  | "RuntimeChecks" => pure (.runtimeChecks)
  | other => throw s!"unrecognized operandVariant tag `{other}`"

def projectionVariant (tag : String) : Except String ProjectionVariant :=
  match tag with
  | "Deref" => pure (.deref)
  | "Field" => pure (.field)
  | "Index" => pure (.index)
  | "ConstantIndex" => pure (.constantIndex)
  | "Subslice" => pure (.subslice)
  | "Downcast" => pure (.downcast)
  | "OpaqueCast" => pure (.opaqueCast)
  | "UnwrapUnsafeBinder" => pure (.unwrapUnsafeBinder)
  | "PhantomDeref" => pure (.phantomDeref)
  | other => throw s!"unrecognized projectionVariant tag `{other}`"

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

inductive Domain where
  | any | statement | terminator | rvalue | operand | projection
  | statementWrapper | terminatorWrapper
  deriving BEq, Hashable

def asTag? (j : Json) (key : String) : Option String :=
  match optionalField j key with
  | none => none
  | some value => match value.getStr? with | .ok text => some text | .error _ => none

def isTypeRef (j : Json) : Option Nat := j.getNat?.toOption

def isAllocationRef (j : Json) : Option Nat := do
  j.getNat?.toOption

def referenceField (parent : Json) (key : String) (value : Json) : Option TypedValue := do
  let id ← value.getNat?.toOption
  if ["span", "root_span", "function_span", "preamble_def_span", "callsite_span"].contains key then return .sourceSpan id
  if ["allocation", "vtable_allocation"].contains key then return .allocationRef id
  if key == "instance_id" then return .instanceRef id
  if ["type", "field_type", "cast_type", "inner_type", "target_type", "element_type",
      "pointee_type", "function_type", "drop_type", "clone_type", "coroutine_type",
      "input_type", "query_input_type", "pointee", "element", "inner", "output",
      "source_type", "base"].contains key || key.endsWith "_type" then return .typeRef id
  if key == "value" && (parent.getObjVal? "kind" >>= Json.getStr?).toOption == some "type" then
    return .typeRef id
  none

def childDomain (parent : Domain) (key : String) : Domain :=
  match parent, key with
  | .statementWrapper, "kind" => .statement
  | .terminatorWrapper, "kind" => .terminator
  | _, "rvalue" => .rvalue
  | _, "operand" | _, "function" | _, "condition" | _, "discriminant" => .operand
  | _, "projection" => .projection
  | _, "statements" => .statementWrapper
  | _, "terminator" => .terminatorWrapper
  | _, _ => .any

def isKnownStatement (tag : String) : Bool :=
  (statementVariant tag).isOk
def isKnownTerminator (tag : String) : Bool :=
  (terminatorVariant tag).isOk
def isKnownRvalue (tag : String) : Bool :=
  (rvalueVariant tag).isOk
def isKnownOperand (tag : String) : Bool :=
  (operandVariant tag).isOk
def isKnownProjection (tag : String) : Bool :=
  (projectionVariant tag).isOk

def recognizedAutoDomain (j : Json) : Option Domain :=
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

def domainTag (j : Json) (domain : Domain) : Option String :=
  match domain with
  | .statement | .terminator | .statementWrapper | .terminatorWrapper => asTag? j "variant"
  | .rvalue | .operand | .projection => asTag? j "kind"
  | .any => none

def isStringJson (j : Json) : Bool :=
  match j with | .str _ => true | _ => false

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

def parseOperatorTag (j : Json) (path : String) : Except String String := do
  match j with
  | .str tag => pure tag
  | .obj _ => fieldString j "kind" path
  | _ => throw s!"{path}: expected tagged operator object"

def typedEnumCategory? (key path : String) (parentTag : Option String) (j : Json) : Option TypedEnumTag := Id.run do
  let hasKind := (optionalField j "kind").isSome
  match key with
  | "value" => if parentTag == some "const" && hasKind then some .typeConstKind else none
  | "const" => if parentTag == some "type_system_const" && hasKind then some .typeConstKind else none
  | "length" =>
    if (parentTag == some "array" || parentTag == some "Repeat") && hasKind then some .typeConstKind else none
  | "start" | "end" =>
    if parentTag == some "range" && hasKind then some .typeConstKind else none
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
    if hasKind then some .mirPhase
    else if isStringJson j then some .mirPhaseStage
    else none
  | "retag" => if hasKind then some .withRetag else none
  | "check" => if parentTag == some "RuntimeChecks" && hasKind then some .runtimeCheck else none
  | "cause" => if hasKind then some .fakeReadCause else none
  | "call_source" => if hasKind then some .callSource else none
  | "reason" =>
    if parentTag == some "BackwardIncompatibleDropHint" && hasKind then
      some .backwardDropReason
    else if hasKind then some .unwindReason
    else none
  | "region" => if hasKind then some .regionKind else none
  | "bound_kind" => if hasKind then some .boundRegionKind else none
  | "index_kind" => if hasKind then some .boundVarIndexKind else none
  | "parameter" => if path.endsWith ".region" && hasKind then some .lateParamRegionKind else none
  | "signed_kind" | "unsigned_kind" | "integer_kind" => if isStringJson j then some .integerType else none
  | "float_kind" => if isStringJson j then some .floatType else none
  | "adt_kind" => if isStringJson j then some .adtKind else none
  | "variance" => if hasKind then some .variance else none
  | "coverage" => if parentTag == some "Coverage" && hasKind then some .coverageKind else none
  | "point_kind" => if path.endsWith ".coverage" && isStringJson j then some .coveragePointKind else none
  | "retag_mode" => if isStringJson j then some .fakeBorrowRetagMode else none
  | _ => none

def parseInlineTag (j : Json) (path : String) : Except String TaggedNode := do
  match j with
  | .str tag => return ⟨tag, j⟩
  | .obj _ =>
    let tag ← fieldString j "kind" path
    return ⟨tag, j⟩
  | _ => throw s!"{path}: expected enum tag object or string"

def userTypeProjectionKind (j : Json) (path : String) : Except String UserTypeProjectionKind := do
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
  | other => throw s!"{path}: unrecognized user type projection `{other}`"

def parseUserTypeProjection (j : Json) (path : String) : Except String UserTypeProjection := do
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
  if (baseIndex.isNone || projections.isNone) then
    throw s!"{path}: supported user-type projection is missing base index or projection sequence"
  return ⟨baseIndex, projections, j⟩

def enumTagKnown (category : TypedEnumTag) (tag : String) : Bool :=
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
      tag == "static" || tag == "placeholder" || tag == "erased"
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
  | .typeConstKind => tag == "value" || tag == "alias" || tag == "expression"

def validateValueLocal (value : TypedValue) (path : String) : Except String Unit := do
  match value with
  | .scalar _ | .diagnostic _ | .typeRef _ | .allocationRef _ | .instanceRef _
  | .localRef _ | .blockRef _ | .sourceSpan _ | .sourceInfo _ => return ()
  | .binOperator _ | .unOperator _ => return ()
  | .enumTag category tag children => do
      if !enumTagKnown category tag.tag then
        throw s!"{joinPath path "kind"}: unrecognized pinned MIR enum tag `{tag.tag}`; update decoder and review its semantics"
      if category == .mirPhase then
        let phaseValue := children.find? fun (key, _) => key == "phase"
        match tag.tag with
        | "built" =>
          if phaseValue.isSome then throw s!"{path}: built MIR phase must not include a subphase"
        | "analysis" | "runtime" =>
          match phaseValue with
          | none => throw s!"{joinPath path "phase"}: analysis/runtime MIR phase is missing its subphase"
          | some (_, .enumTag .mirPhaseStage phaseTag _) =>
            let valid := if tag.tag == "analysis" then
              phaseTag.tag == "initial" || phaseTag.tag == "post_cleanup"
              else phaseTag.tag == "initial" || phaseTag.tag == "post_cleanup" || phaseTag.tag == "optimized"
            if !valid then throw s!"{joinPath path "phase"}: subphase `{phaseTag.tag}` does not belong to `{tag.tag}` MIR"
          | some (_, _) => throw s!"{joinPath path "phase"}: MIR subphase is not a typed tag"
        | _ => pure ()
      if category == .withRetag then
        let performs := children.find? fun (key, _) => key == "performs_retag"
        match performs with
        | some (_, .scalar (.bool value)) =>
          if value != (tag.tag == "yes") then throw s!"{joinPath path "performs_retag"}: boolean disagrees with the WithRetag tag"
        | _ => throw s!"{joinPath path "performs_retag"}: WithRetag tag is missing its boolean witness"
      if category == .runtimeCheck then
        match children.find? fun (key, _) => key == "enabled" with
        | some (_, .scalar (.bool _)) => pure ()
        | _ => throw s!"{joinPath path "enabled"}: runtime-check tag is missing its configured boolean"
      if category == .coverageKind then
        let hasNatField := fun key =>
          match children.find? fun (fieldKey, _) => fieldKey == key with
          | some (_, .scalar (.num value)) => ((Json.num value).getNat?).isOk
          | _ => false
        match tag.tag with
        | "point" =>
          match children.find? fun (key, _) => key == "point_kind" with
          | some (_, .enumTag .coveragePointKind _ _) => pure ()
          | _ => throw s!"{joinPath path "point_kind"}: coverage point is missing its typed point kind"
          match children.find? fun (key, _) => key == "hir_id" with
          | some (_, .object fields) =>
            let hasOwner := fields.any fun (key, value) =>
              key == "owner_def_id" && match value with
                | .scalar (.num number) => ((Json.num number).getNat?).isOk
                | _ => false
            let hasLocalId := fields.any fun (key, value) =>
              key == "local_id" && match value with
                | .scalar (.num number) => ((Json.num number).getNat?).isOk
                | _ => false
            if !hasOwner || !hasLocalId then
              throw s!"{joinPath path "hir_id"}: coverage point has malformed owner DefId or local HIR index"
          | _ => throw s!"{joinPath path "hir_id"}: coverage point is missing its HIR identifier"
        | "block_marker" =>
          if !hasNatField "id" then throw s!"{joinPath path "id"}: block-marker coverage is missing its identifier"
        | "virtual_counter" =>
          if !hasNatField "bcb" then throw s!"{joinPath path "bcb"}: virtual-counter coverage is missing its basic-block counter"
        | _ => pure ()
      if category == .regionKind then
        let hasField := fun key => (children.find? fun (fieldKey, _) => fieldKey == key).isSome
        match tag.tag with
        | "early_parameter" =>
          if !hasField "index" || !hasField "name" then
            throw s!"{path}: early region parameter is missing its index or name"
        | "bound" =>
          if !hasField "index_kind" || !hasField "variable_index" || !hasField "bound_kind" then
            throw s!"{path}: bound region is missing index, variable, or bound-kind metadata"
        | "late_parameter" =>
          if !hasField "scope_def_id" || !hasField "scope_def_path" || !hasField "parameter" then
            throw s!"{path}: late region parameter is missing its scope or parameter metadata"
        | "inference_variable" | "placeholder" =>
          if !hasField "index" && !hasField "universe" then
            throw s!"{path}: region variable is missing its identifying metadata"
        | _ => pure ()
      return ()
  | .userTypeProjection projection => do
      if projection.baseIndex.isNone then
        throw s!"{joinPath path "base_index"}: user-type projection is missing its base annotation index"
      if projection.projections.isNone then
        throw s!"{joinPath path "projections"}: user-type projection is missing its projection sequence"
      return ()
  | .array _ => return ()
  | .object _ => return ()
  | .statement variant fields => do
      match variant with
      | .ascribeUserType =>
        if !(fields.any fun (key, value) => key == "user_type_projection" && match value with | .userTypeProjection _ => true | _ => false) then
          throw s!"{joinPath path "user_type_projection"}: supported AscribeUserType is missing typed projection data"
        if !(fields.any fun (key, value) => key == "variance" && match value with | .enumTag .variance _ _ => true | _ => false) then
          throw s!"{joinPath path "variance"}: supported AscribeUserType is missing typed variance data"
      | .coverage =>
        if !(fields.any fun (key, value) => key == "coverage" && match value with | .enumTag .coverageKind _ _ => true | _ => false) then
          throw s!"{joinPath path "coverage"}: supported Coverage statement is missing its typed coverage kind"
      | _ => pure ()
      return ()
  | .terminator _ _ => return ()
  | .rvalue _ _ => return ()
  | .operand _ _ => return ()
  | .projection _ _ => return ()


abbrev DecodeValueM := Except String

mutual
partial def decodeValueM (j : Json) (path : String) (domain : Domain)
    (tagCategory : Option TypedEnumTag) : DecodeValueM TypedValue := do
  let value ← decodeValueBody j path domain tagCategory
  validateValueLocal value path
  pure value

partial def decodeValueBody (j : Json) (path : String) (domain : Domain)
    (tagCategory : Option TypedEnumTag) : DecodeValueM TypedValue := do
  if statusOf? j == some "debug_payload" then return .diagnostic j
  match j with
  | .arr values =>
    let mut decoded := #[]
    let mut index := 0
    for value in values do
      decoded := decoded.push (← decodeValueM value s!"{path}[{index}]" domain tagCategory)
      index := index + 1
    return .array decoded
  | .obj _ =>
    if hasField j "span" && hasField j "scope" then
      return .sourceInfo (← parseSourceInfo j path)
    let effectiveDomain := if domain == .any then
      match recognizedAutoDomain j with | some detected => detected | none => .any
      else domain
    let fields ← objectFields j
    let mut decodedFields := #[]
    let parentTag := match effectiveDomain with
      | .rvalue | .operand | .statement | .terminator => domainTag j effectiveDomain
      | _ => asTag? j "kind"
    for (key, value) in fields do
      let nextDomain := childDomain effectiveDomain key
      let decoded ← if let some reference := referenceField j key value then pure reference
        else if key == "line_spans" then do
          let spans ← value.getArr?
          return .array (← spans.mapM fun span => TypedValue.sourceSpan <$> span.getNat?)
        else if key == "user_type_projection" && parentTag == some "AscribeUserType" then
          .userTypeProjection <$> parseUserTypeProjection value (joinPath path key)
        else if key == "operator" && (parentTag == some "BinaryOp" || optionalField j "kind" == some (.str "Overflow")) then
          let tag ← parseOperatorTag value (joinPath path key)
          match binOpFromExportTag tag with
          | some op => pure (.binOperator op)
          | none => throw s!"{joinPath path "operator"}: unrecognized binary operator `{tag}`"
        else if key == "operator" && parentTag == some "UnaryOp" then
          let tag ← parseOperatorTag value (joinPath path key)
          match unOpFromExportTag tag with
          | some op => pure (.unOperator op)
          | none => throw s!"{joinPath path "operator"}: unrecognized unary operator `{tag}`"
        else decodeValueM value (joinPath path key) nextDomain (typedEnumCategory? key path parentTag value)
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
      return .statement (← statementVariant tag) decodedFields
    | .terminator =>
      let tag ← fieldString j "variant" path
      return .terminator (← terminatorVariant tag) decodedFields
    | .rvalue =>
      let tag ← fieldString j "kind" path
      if tag == "BinaryOp" || tag == "UnaryOp" then
        let operator ← field j "operator" path
        let _ ← parseOperatorTag operator (joinPath path "operator")
      return .rvalue (← rvalueVariant tag) decodedFields
    | .operand =>
      let tag ← fieldString j "kind" path
      return .operand (← operandVariant tag) decodedFields
    | .projection =>
      let tag ← fieldString j "kind" path
      return .projection (← projectionVariant tag) decodedFields
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


def decodeValue (j : Json) (path : String) (domain : Domain := .any)
    (tagCategory : Option TypedEnumTag := none) : Except String TypedValue := do
  decodeValueM j path domain tagCategory

def jsonArray (j : Json) (path : String) : Except String (Array Json) :=
  j.getArr? |>.mapError fun e => s!"{path}: expected array ({e})"

def natArray (j : Json) (path : String) : Except String (Array Nat) := do
  let values ← jsonArray j path
  let mut out := #[]
  let mut index := 0
  for value in values do
    out := out.push (← value.getNat? |>.mapError fun e => s!"{path}[{index}]: expected unsigned integer ({e})")
    index := index + 1
  return out

def optionalNat (j : Json) (key path : String) : Except String (Option Nat) := do
  match optionalField j key with
  | none | some .null => pure none
  | some value => (value.getNat?).map some |>.mapError fun e => s!"{joinPath path key}: expected unsigned integer or null ({e})"

def optionalJson (j : Json) (key : String) : Option Json :=
  optionalField j key |>.filter (· != .null)

def parseTagged (j : Json) (path : String) : Except String TaggedNode := do
  let tag ← fieldString j "kind" path
  return ⟨tag, j⟩

def parseAbiTag (j : Json) (path : String) : Except String TaggedNode := do
  match j with
  | .str tag => return ⟨tag, j⟩
  | .obj _ =>
    let tag ← match optionalField j "kind" with
      | some value => value.getStr? |>.mapError fun e => s!"{joinPath path "kind"}: expected string enum tag ({e})"
      | none => match optionalField j "variant" with
        | some value => value.getStr? |>.mapError fun e => s!"{joinPath path "variant"}: expected string enum tag ({e})"
        | none => throw s!"{path}: enum object is missing its kind tag"
    return ⟨tag, j⟩
  | _ => throw s!"{path}: expected enum tag string or tagged object"

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

def optionalNatBefore (j : Json) (key path : String) : Except String (Option Nat) := do
  match optionalField j key with
  | none | some .null => pure none
  | some value => (value.getNat?).map some |>.mapError fun e => s!"{joinPath path key}: expected unsigned integer or null ({e})"

def parsePrimitiveLayout (j : Json) (path : String) : Except String PrimitiveLayout := do
  let tag ← fieldString j "kind" path
  let kind : PrimitiveKind ← match tag with
    | "integer" => pure (.integer)
    | "float" => pure (.float)
    | "pointer" => pure (.pointer)
    | other => throw s!"{path}: unrecognized PrimitiveKind `{other}`"
  let integerKindText ← optionalString j "integer_kind" path
  let integerKind ← integerKindText.mapM integerTypeTag
  let signed ← match optionalField j "signed" with
    | none | some .null => pure none
    | some value => (value.getBool?).map some |>.mapError fun e => s!"{joinPath path "signed"}: expected boolean ({e})"
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
    payload := j
  }

def parseU128Natural (j : Json) (path : String) : Except String Nat := do
  let text ← j.getStr? |>.mapError fun error => s!"{path}: expected exact unsigned decimal string ({error})"
  unless !text.isEmpty && text.toList.all Char.isDigit do throw s!"{path}: expected exact unsigned decimal string"
  let some value := text.toNat? | throw s!"{path}: invalid unsigned decimal"
  unless value < 2^128 do throw s!"{path}: u128 overflow"
  pure value

def parseScalarLayout (j : Json) (path : String) : Except String ScalarLayout := do
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
    payload := j
  }

def parseNicheLayout (j : Json) (path : String) : Except String (Option NicheLayout) := do
  if j == .null then return none
  let range ← field j "valid_range" path
  return some {
    offsetBytes := ← fieldNat j "offset_bytes" path
    primitive := ← parsePrimitiveLayout (← field j "primitive" path) (joinPath path "primitive")
    validRange := (← parseU128Natural (← field range "start" (joinPath path "valid_range")) (joinPath path "valid_range.start"),
      ← parseU128Natural (← field range "end" (joinPath path "valid_range")) (joinPath path "valid_range.end"))
  }

def parseBackendRepr (j : Json) (path : String) : Except String BackendRepr := do
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

def parseFieldShape (j : Json) (path : String) : Except String FieldShape := do
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
    payload := j
  }

def parseLayoutVariant (j : Json) (path : String) : Except String LayoutVariant := do
  return {
    fields := ← parseFieldShape (← field j "fields" path) (joinPath path "fields")
    largestNiche := ← parseNicheLayout (← field j "largest_niche" path) (joinPath path "largest_niche")
    variantIndex := ← fieldNat j "variant_index" path
    sizeBytes := ← fieldNat j "size_bytes" path
    backendRepr := ← parseBackendRepr (← field j "backend_repr" path) (joinPath path "backend_repr")
    fieldOffsetsBytes := ← natArray (← field j "field_offsets_bytes" path) (joinPath path "field_offsets_bytes")
    uninhabited := ← fieldBool j "uninhabited" path
    payload := j
  }

def decimalNat (text path : String) : Except String Nat := do
  if text.isEmpty then throw s!"{path}: expected a nonempty unsigned decimal integer"
  let mut value := 0
  for digit in text.toList do
    if digit < '0' || digit > '9' then throw s!"{path}: expected an unsigned decimal integer"
    value := value * 10 + digit.toNat - '0'.toNat
  return value

def parseTagEncoding (j : Json) (path : String) : Except String TagEncoding := do
  match j with
  | .str _ =>
    throw s!"{path}: tag encoding must be a typed object"
  | .obj _ =>
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
      | none | some .null => pure none
      | some value =>
        let text ← value.getStr? |>.mapError fun e => s!"{joinPath path "niche_start"}: expected exact decimal string ({e})"
        pure (some (← decimalNat text (joinPath path "niche_start")))
    match kind with
    | .direct => pure ()
    | .niche =>
      if (untaggedVariant.isNone || nicheVariants.isNone || nicheStart.isNone) then
        throw s!"{path}: supported niche tag encoding is missing its range or start value"
    return ⟨kind, untaggedVariant, nicheVariants, nicheStart, j⟩
  | _ => throw s!"{path}: expected structured tag encoding"

def parseVariantsLayout (j : Json) (path : String) : Except String VariantsLayout := do
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
    payload := j
  }

def parseLayout (j : Json) (path : String) : Except String Layout := do
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
    payload := j
  }

def parseFunctionSignature (j : Json) (path : String) : Except String FunctionSignature := do
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
  let normalized ← match normalization with
    | .null => pure none
    | value => value.getNat?.map some
  pure {
    id := ← fieldNat j "predicate_id" "$predicate"
    typingEnvironment := ← fieldString j "typing_env" "$predicate"
    stableKey := ← fieldNat j "stable_key" "$predicate"
    autoTrait := ← fieldBool j "auto_trait" "$predicate"
    normalizedId := normalized
    original := ← fieldNat j "original" "$predicate"
    payload := j }

/-- Decode all source PatternKind branches; unknown kinds fail explicitly. -/
partial def decodeCompilerPattern (j : Json) : Except String CompilerPattern := do
  match ← fieldString j "kind" "$pattern" with
  | "range" => return .range (← fieldNat j "start" "$pattern") (← fieldNat j "end" "$pattern")
  | "or" => return .or (← (← arrayField j "patterns" "$pattern").mapM decodeCompilerPattern)
  | "not_null" => pure .notNull
  | _ => throw "unknown compiler PatternKind"

private def parseProjectionQueries (j : Json) (path : String) : Except String ProjectionQueries := do
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

private def parseDiscriminants (j : Json) (path : String) : Except String DiscriminantInfo := do
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
def decodeTypeCompilerFacts (j : Json) (path : String := "$compiler_facts") : Except String TypeCompilerFacts := do
  let some inputType := isTypeRef (← field j "input_type" path) | throw "compiler fact input_type is not a type reference"
  let mut booleans := #[]
  for (name,value) in ← objectFields (← field j "boolean_queries" path) do
    let result ← value.getBool?
    booleans := booleans.push (name, result)
  let mut types := #[]
  for (name,value) in ← objectFields (← field j "type_queries" path) do
    let result ← match value with
      | .null => pure none
      | value => match isTypeRef value with
        | some id => pure (some id)
        | none => throw "compiler type query value is not a type reference or null"
    types := types.push (name, result)
  let captureNames ← match optionalField j "capture_names" with
    | none => pure none
    | some query => do
      let names ← match query with
        | .null => pure none
        | .arr names => (names.mapM fun (name : Json) => match name with
            | .null => pure none
            | name => name.getStr?.map some).map some
        | _ => throw "capture_names must be null or array"
      pure names
  let adt ← match ← field j "adt" path with
    | .null => pure none
    | value => do
      let definitionId ← fieldNat value "definition" path
      let itemName ← fieldString value "item_name" path
      let nonnullOptimizationGuaranteed ← fieldBool value "nonnull_optimization_guaranteed" path
      pure (some ({ definitionId, itemName, nonnullOptimizationGuaranteed } : AdtCompilerFacts))
  let projectionQueries ← match ← field j "projection_queries" path with
    | .null => pure none
    | value => some <$> parseProjectionQueries value (joinPath path "projection_queries")
  let simdSizeAndType : Option (Nat × TypeId) ← match ← field j "simd_size_and_type" path with
    | .null => pure none
    | value => do
      let count ← fieldNat value "count" path
      unless count < 2^64 do throw s!"{path}: SIMD lane count exceeds u64"
      let element ← fieldNat value "element" path
      pure (some (count, element))
  let discriminants ← match ← field j "discriminants" path with
    | .null => pure none
    | value => some <$> parseDiscriminants value (joinPath path "discriminants")
  let typeIdHash ← match optionalField j "type_id_hash" with
    | none => pure none
    | some value => do
      let bits ← decimalNat (← value.getStr?) (joinPath path "type_id_hash")
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

private def parseReprOptions (j : Json) (path : String) : Except String ReprOptions := do
  let integer ← match ← field j "integer" path with
    | .null => pure none
    | value =>
      let result ← match ← fieldString value "kind" path with
        | "pointer_sized" => do
          pure (ReprInteger.pointerSized (← fieldBool value "signed" path))
        | "fixed" => do
          pure (ReprInteger.fixed (← integerTypeTag (← fieldString value "integer_kind" path))
            (← fieldNat value "size_bits" path) (← fieldBool value "signed" path))
        | _ => throw s!"{path}.integer: unknown representation integer"
      pure (some result)
  let scalableElement ← match ← field j "scalable_element" path with
    | .null => pure none
    | value =>
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

private def parseAdtShape (j : Json) (path : String) : Except String AdtShape := do
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

private def parseShapeMutability (j : Json) (path : String) : Except String Miri.MIR.Mutability := do
  match ← fieldString j "kind" path with
  | "mutable" => pure .Mut
  | "immutable" => pure .Not
  | _ => throw s!"{path}: unknown mutability"

private def parseShapeBoundVariables (j : Json) (key path : String) :
    Except String (Array Miri.MIR.BoundVariableKind) := do
  (← arrayField j key path).mapM GenericArgsCodec.boundVariable

private def parseTypeShape (j : Json) (path : String) : Except String TypeShape := do
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
    let predicates ← (← arrayField j "predicates" path).mapM Json.getNat?
    return .dynamicTraitObject predicates (← optionalNatField j "principal_predicate" path) (← region)
  | "closure" => return .closure (← definition) (← args) (← fieldNat j "upvar_count" path)
  | "coroutine_closure" => return .coroutineClosure (← definition) (← args)
  | "coroutine" => return .coroutine (← definition) (← args)
  | "never" => pure .never
  | "tuple" => return .tuple (← (← arrayField j "elements" path).mapM Json.getNat?)
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

def parseTypeNode (j : Json) (path : String) : Except String TypeNode := do
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

def parseInitRange (j : Json) (path : String) : Except String InitRange := do
  let state ← fieldString j "state" path
  let initialized ← match state with
    | "initialized" => pure true
    | "uninitialized" => pure false
    | _ => throw s!"{joinPath path "state"}: unrecognized initialization state `{state}`"
  let first ← fieldNat j "start_bytes" path
  let last ← fieldNat j "end_bytes_exclusive" path
  if last < first then throw s!"{path}: initialization range has end before start"
  return ⟨initialized, first, last⟩

def parseRelocation (j : Json) (path : String) : Except String Relocation := do
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

def parseAllocationMemory (j : Json) (path : String) : Except String AllocationMemory := do
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

def parseDefinitionId (j : Json) (path : String) : Except String DefinitionId := do
  return ⟨← fieldNat j "crate" path, ← fieldNat j "index" path⟩

def parseDefinitionRef (j : Json) (path : String) : Except String DefinitionRef :=
  j.getNat? |>.mapError fun error => s!"{path}: expected definition ID ({error})"

def parseSelectedScope (j : Json) (path : String) : Except String SelectedScope := do
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
    payload := j
  }

def vtablePredicateKind (tag : String) : Except String VtablePredicateKind :=
  match tag with
  | "trait" => pure (.trait)
  | "auto_trait" => pure (.autoTrait)
  | "projection" => pure (.projection)
  | other => throw s!"unrecognized vtablePredicateKind tag `{other}`"

def parseVtablePredicate (j : Json) (path : String) : Except String VtablePredicate := do
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
  let boundVariables ← ((← arrayField j "bound_variables" path).toList.zipIdx.mapM fun ((value, index) : Json × Nat) =>
    GenericArgsCodec.boundVariable value |>.mapError fun error => s!"{path}.bound_variables[{index}]: {error}").map List.toArray
  return {
    kind
    definitionId := ← fieldNat j "def_id" path
    definitionPath := ← optionalString j "def_path" path
    genericArgs
    boundVariables
    projectionTerm
    payload := j
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

def parseVtableEntry (j : Json) (path : String) : Except String VtableEntry := do
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
    payload := j
  }

def parseAllocation (j : Json) (path : String) : Except String AllocationNode := do
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
      definitionId := ← parseDefinitionRef (← field j "def_id" path) (joinPath path "def_id")
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
      predicates := predicates.push (← predicate.getNat? |>.mapError fun error => s!"{joinPath path "predicates"}[{index}]: expected predicate ID ({error})")
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
      payload := j
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
    payload := j
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

def parseSourceAllocIdPoolRow (j : Json) (path : String) : Except String SourceAllocIdPoolRow := do
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

def parseSourceAllocIdSaltResult (j : Json) (path : String) : Except String SourceAllocIdSaltResult := do
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

def parseSourceAllocIdDedupRow (j : Json) (path : String) : Except String SourceAllocIdDedupRow := do
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

def parseCompilerAllocIdWorld (j : Json) (nodes : Array AllocationNode) : Except String CompilerAllocIdWorld := do
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
      let expectedKind ← match row.kind with
        | .memory => pure AllocationKind.memory
        | .function => pure AllocationKind.function
        | .vtable => pure AllocationKind.vtable
        | .static => pure AllocationKind.static
        | .typeId => pure AllocationKind.typeId
        | .dangling => throw s!"{rowPath}: dangling source global cannot be serialized"
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
    else if nodeIndexBySourceId.contains row.sourceAllocId.toNat then
      throw s!"{rowPath}: non-serialized source ID is attached to an allocation node"
    pool := pool.push row
  let some sentinel := pool[pool.size - 1]? | throw "$.compiler_alloc_id_world.raw_pool: sentinel row absent"
  unless sentinel.kind == .dangling && sentinel.status == .dangling && sentinel.allocationId.isNone do
    throw "$.compiler_alloc_id_world.raw_pool: final reserved sentinel must be dangling"
  for node in nodes do
    let some sourceId := node.sourceAllocId | throw "$.compiler_alloc_id_world: every imported allocation must carry an exact source_alloc_id witness"
    let some row := pool[sourceId.toNat - 1]? | throw "$.compiler_alloc_id_world: allocation witness lies outside captured raw prefix"
    unless row.status == .serialized && row.allocationId == some node.id do
      throw "$.compiler_alloc_id_world: allocation node is not covered by exactly one serialized pool row"
  let dedupJson ← arrayField j "dedup_catalog" path
  let mut dedup := #[]
  let mut byteRowByImage : Std.HashMap String Nat := {}
  let mut functionRowByInstance : Std.HashMap InstanceId Nat := {}
  let mut vtableRowsByType : Std.HashMap TypeId (Array (Array Nat)) := {}
  let mut staticDefinitionsSeen : Std.HashMap Nat Nat := {}
  let mut typeIdRowByType : Std.HashMap TypeId Nat := {}
  for (value, index) in dedupJson.toList.zipIdx do
    let rowPath := s!"$.compiler_alloc_id_world.dedup_catalog[{index}]"
    let row ← parseSourceAllocIdDedupRow value rowPath
    unless #[.bytes, .function, .vtable, .static, .typeId].contains row.keyKind do
      throw s!"{rowPath}.key_kind: dedup key family is not available in this prepared profile"
    let some keyIndex := nodeIndexByGraphId[row.keyAllocationId]? | throw s!"{rowPath}.key_allocation_id: selected key node is not serialized"
    let some keyNode := nodes[keyIndex]? | throw s!"{rowPath}.key_allocation_id: selected key index is absent"
    let expectedKeyKind ← match row.keyKind with
      | .bytes => pure AllocationKind.memory
      | .function => pure AllocationKind.function
      | .vtable => pure AllocationKind.vtable
      | .static => pure AllocationKind.static
      | .typeId => pure AllocationKind.typeId
      | _ => throw s!"{rowPath}: unavailable dedup key family"
    unless keyNode.kind == expectedKeyKind do
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
      unless resultNode.kind == expectedKeyKind do
        throw s!"{rowPath}.salts[{saltIndex}]: result allocation has incompatible kind/status"
      if row.keyKind == .function then
        let some (.function keyFunction) := keyNode.data
          | throw s!"{rowPath}: function key witness lacks typed instance data"
        let some (.function resultFunction) := resultNode.data
          | throw s!"{rowPath}.salts[{saltIndex}]: function result lacks typed instance data"
        unless keyFunction.instanceId == resultFunction.instanceId do
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
      let defKey := keyStatic.definitionId
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
    if let some (.function fn) := node.data then
      unless functionRowByInstance.contains fn.instanceId do
        throw "$.compiler_alloc_id_world.dedup_catalog: selected function node lacks its exact full-salt key outcomes"
    if let some (.vtable vtable) := node.data then
      unless (vtableRowsByType[vtable.typeId]?.getD #[]).contains vtable.predicates do
        throw "$.compiler_alloc_id_world.dedup_catalog: selected vtable node lacks its exact full-salt key outcomes"
    if let some (.static static) := node.data then
      unless staticDefinitionsSeen.contains static.definitionId do
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
  let nonExhaustiveJson ← arrayField j "non_exhaustive_key_families" path
  let mut nonExhaustiveFamilies := #[]
  for (family, index) in nonExhaustiveJson.toList.zipIdx do
    let name ← family.getStr? |>.mapError fun _ => s!"$.compiler_alloc_id_world.non_exhaustive_key_families[{index}]: expected string"
    let kind ← parseSourceAllocIdDedupKind name s!"$.compiler_alloc_id_world.non_exhaustive_key_families[{index}]"
    unless #[.function, .vtable, .static, .typeId, .memory].contains kind do
      throw s!"$.compiler_alloc_id_world.non_exhaustive_key_families[{index}]: unknown or inapplicable non-exhaustive family"
    if nonExhaustiveFamilies.contains kind then throw "$.compiler_alloc_id_world.non_exhaustive_key_families: duplicate family"
    if completeFamilies.contains kind then throw "$.compiler_alloc_id_world: key family is both complete and non-exhaustive"
    nonExhaustiveFamilies := nonExhaustiveFamilies.push kind
  for required in #[SourceAllocIdDedupKind.function, .vtable, .static, .typeId, .memory] do
    unless nonExhaustiveFamilies.contains required do
      throw "$.compiler_alloc_id_world.non_exhaustive_key_families: function/vtable/static/type_id/memory_const_allocation must remain explicitly non-exhaustive"
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
    nonExhaustiveKeyFamilies := nonExhaustiveFamilies
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
          parsed.kind == supplied.kind &&
          parsed.memory == supplied.memory && parsed.data == supplied.data &&
          parsed.payload.compress == supplied.payload.compress do
        throw s!"$.allocations[{index}]: source AllocId profile does not match the exact raw allocation node"
    let verified ← parseCompilerAllocIdWorld rawWorld nodes
    unless verified == world do
      throw "source AllocId profile model does not match its exact raw document object"

def parseLocal (j : Json) (path : String) : Except String LocalDecl := do
  let type ← field j "type" path
  let typeId ← match isTypeRef type with
    | some id => pure id
    | none => throw s!"{joinPath path "type"}: expected type reference object"
  let sourceInfo ← parseSourceInfo (← field j "source_info" path) (joinPath path "source_info")
  return {
    id := ← fieldNat j "local" path
    typeId := typeId
    sourceInfo := sourceInfo
    payload := j
  }

def parseMirNode (wrapper : Json) (path : String) (domain : Domain) : Except String MirNode := do
  let sourceInfo ← parseSourceInfo (← field wrapper "source_info" path) (joinPath path "source_info")
  let kind ← field wrapper "kind" path
  let value ← decodeValue kind (joinPath path "kind") domain .none
  return ⟨value, sourceInfo⟩

def parseCallResolution (j : Json) (path : String) : Except String CallResolutionEvidence := do
  let tag ← fieldString j "kind" path
  let kind ← match tag with
    | "resolved_instance" => pure CallResolutionKind.direct
    | "virtual_dispatch" => pure .virtualDispatch
    | "indirect_function_pointer" => pure .indirect
    | _ => throw s!"{path}: unsupported compiler call resolution"
  let instanceId ← if kind == .indirect then pure none else some <$> fieldNat j "instance_id" path
  let functionType ← some <$> fieldNat j "function_type" path
  let dispatchSlot ← if kind == .virtualDispatch then some <$> fieldNat j "dispatch_slot" path else pure none
  return { kind, instanceId, functionType, dispatchSlot, fnAbiId := ← fieldNat j "fn_abi" path, payload := j }

def parseSourceScope (j : Json) (path : String) : Except String SourceScope := do
  let inlined ← match ← field j "inlined" path with
    | .null => pure none
    | value => do
      let instanceId ← fieldNat value "instance_id" path
      let callsiteSpanId ← fieldNat value "callsite_span" path
      let requiresCallerLocation ← fieldBool value "requires_caller_location" path
      pure (some ({ instanceId, callsiteSpanId, requiresCallerLocation } : InlinedScope))
  return {
    id := ← fieldNat j "scope" path
    parent := ← optionalNatField j "parent" path
    spanId := ← fieldNat j "span" path
    inlined
    inlinedParent := ← optionalNatField j "inlined_parent_scope" path
  }

def parseBacktraceSpan (j : Json) (path : String) : Except String BacktraceSpan := do
  let source ← field j "source_position" path
  let bytePosition ← fieldNat source "byte_position" path
  let line ← fieldNat source "line" path
  let column ← fieldNat source "zero_based_char_column" path
  let filename ← fieldString source "filename" path
  return {
    spanId := ← fieldNat j "span" path
    collapsedLo := ← fieldNat j "collapsed_lo" path
    position := { bytePosition, line, column, filename }
  }

def parseBasicBlock (j : Json) (path : String) : Except String BasicBlock := do
  let statementJson ← arrayField j "statements" path
  let mut statements := #[]
  let mut index := 0
  for statement in statementJson do
    statements := statements.push (← parseMirNode statement s!"{joinPath path "statements"}[{index}]" .statement)
    index := index + 1
  let terminatorObject ← field j "terminator" path
  if terminatorObject == .null then throw s!"{joinPath path "terminator"}: basic block has no terminator"
  let kind ← field (← field j "terminator" path) "kind" path
  let callResolution ← if ["Call", "TailCall"].contains ((kind.getObjValAs? String "variant").toOption.getD "") then
    some <$> parseCallResolution (← field kind "resolution" path) (joinPath path "terminator.kind.resolution")
    else pure none
  return {
    callResolution

    id := ← fieldNat j "block" path
    statements := statements
    terminator := ← parseMirNode terminatorObject (joinPath path "terminator") .terminator
    cleanup := ← fieldBool j "is_cleanup" path
    payload := j
  }

private def parseConstantQueryContext (j : Json) (path : String) : Except String ConstantQueryContext := do
  let inputPhase ← match ← fieldString j "mir_input_phase" path with
    | "template" => pure BodyInputPhase.template
    | "already_instantiated" => pure .alreadyInstantiated
    | other => throw s!"{path}: unknown body input phase {other}"
  let normalization ← field j "normalization" path
  let required ← field j "required_constant_checks" path
  let requiredChecks ← ((← arrayField required "checks" path).toList.zipIdx.mapM fun ((check, position) : Json × Nat) => do
    let checkPath := s!"{path}.required_constant_checks.checks[{position}]"
    let result ← field check "result" checkPath
    let index ← fieldNat check "index" checkPath
    let spanId ← fieldNat check "span" checkPath
    let normalizedOperand ← decodeValue (← field result "normalized_operand" checkPath) (joinPath checkPath "normalized_operand")
    let value ← decodeValue (← field result "value" checkPath) (joinPath checkPath "value")
    pure ({ index, spanId, normalizedOperand, value } : RequiredConstantCheck)).map List.toArray
  let instanceId ← fieldNat j "instance_id" path
  let normalizationBodyId ← fieldNat normalization "body" path
  let requiredTypingEnvironment ← fieldString required "typing_env" path
  pure { instanceId, inputPhase, normalizationBodyId, requiredTypingEnvironment, requiredChecks }

def parseBodyCore (j : Json) (path fallbackName : String) : Except String BodyCore := do
  let localsJson ← arrayField j "locals" path
  let mut locals := #[]
  let mut index := 0
  for localDecl in localsJson do
    locals := locals.push (← parseLocal localDecl s!"{joinPath path "locals"}[{index}]")
    index := index + 1
  let blocksJson ← arrayField j "basic_blocks" path
  let mut blocks := #[]
  index := 0
  for block in blocksJson do
    blocks := blocks.push (← parseBasicBlock block s!"{joinPath path "basic_blocks"}[{index}]")
    index := index + 1
  let defPath ← optionalString j "def_path" path
  let definitionId ← match optionalJson j "def_id" with
    | none => match optionalJson j "source_def_id" with
      | none => pure none
      | some value => pure (some (← parseDefinitionRef value (joinPath path "source_def_id")))
    | some value => pure (some (← parseDefinitionRef value (joinPath path "def_id")))
  let phase ← decodeValue (← field j "phase" path) (joinPath path "phase") .any (some .mirPhase)
  let injectionPhase ← match optionalJson j "injection_phase" with
    | none => pure none
    | some value => pure (some (← decodeValue value (joinPath path "injection_phase") .any (some .mirPhase)))
  let sourceScopes ← match optionalJson j "source_scopes" with
    | none => pure none
    | some value => some <$> ((← jsonArray value (joinPath path "source_scopes")).toList.zipIdx.mapM fun ((scope, index) : Json × Nat) =>
      parseSourceScope scope s!"{path}.source_scopes[{index}]").map List.toArray
  let backtraceSpans ← ((← arrayField j "backtrace_spans" path).toList.zipIdx.mapM fun ((value, index) : Json × Nat) =>
    parseBacktraceSpan value s!"{path}.backtrace_spans[{index}]").map List.toArray
  return {
    constantQueryContext := ← match optionalJson j "constant_query_context" with
      | none => pure none
      | some value => some <$> parseConstantQueryContext value (joinPath path "constant_query_context")
    requiredConsts := ← match optionalJson j "required_consts" with
      | none => pure none
      | some value => some <$> ((← jsonArray value (joinPath path "required_consts")).mapM fun item => decodeValue item (joinPath path "required_consts"))
    spanId := ← fieldNat j "span" path
    preambleDefSpanId := ← fieldNat j "preamble_def_span" path
    backtraceSpans

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

def parsePromotedBodies (j : Json) (path _fallbackName : String) : Except String (Array PromotedBody) := do
  let promotedJson ← match optionalJson j "promoted_bodies" with
    | none => pure #[]
    | some value => jsonArray value (joinPath path "promoted_bodies")
  let mut promotedBodies := #[]
  for (entry, index) in promotedJson.toList.zipIdx do
    let promotedPath := s!"{joinPath path "promoted_bodies"}[{index}]"
    let promotedIndex ← match optionalField entry "promoted_index" with
      | none => pure index
      | some value => value.getNat? |>.mapError fun e => s!"{joinPath promotedPath "promoted_index"}: expected unsigned integer ({e})"
    let body ← match optionalJson entry "body" with
      | none => pure none
      | some value => pure (some (← value.getNat?))
    promotedBodies := promotedBodies.push ⟨promotedIndex, body, entry⟩
  return promotedBodies

def parseBody (j : Json) (path fallbackName : String) : Except String Body := do
  let core ← parseBodyCore j path fallbackName
  let promotedBodies ← parsePromotedBodies j path fallbackName
  return { core with promotedBodies := promotedBodies }

def parseBodyRoot (j : Json) (path : String) : Except String BodyRoot := do
  let defPath ← fieldString j "def_path" path
  return {
    bodyId := ← fieldNat j "body" path
    entryInstance := ← fieldNat j "entry_instance" path
    definitionId := ← fieldNat j "def_id" path
    defPath := defPath
    isStatic := ← fieldBool j "is_static" path
    threadLocalStatic := ← fieldBool j "thread_local_static" path
    promotedBodies := ← parsePromotedBodies j path defPath
    payload := j
  }

def parseInstance (j : Json) (path : String) : Except String InstanceNode := do
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
    | none | some .null => pure none
    | some value => (value.getBool?).map some |>.mapError fun e => s!"{joinPath path "body_template_is_polymorphic"}: expected boolean ({e})"
  let instanceArgsAreMonomorphic ← match optionalField j "instance_args_are_monomorphic" with
    | none | some .null => pure none
    | some value => (value.getBool?).map some |>.mapError fun e => s!"{joinPath path "instance_args_are_monomorphic"}: expected boolean ({e})"
  let body ← match optionalJson j "body" with
    | none => pure none
    | some value => pure (some (← value.getNat?))
  let promotedBodies ← parsePromotedBodies j path fallback
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
    payload := j
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

def parseArgumentExtension (j : Json) (path : String) : Except String ArgumentExtensionKind := do
  match ← fieldString j "kind" path with
  | "none" => pure .none
  | "zero_extend" => pure .zeroExtend
  | "sign_extend" => pure .signExtend
  | _ => throw s!"{path}: unrecognized argument extension"

def parseArgumentCapture (j : Json) (path : String) : Except String ArgumentCaptureKind := do
  match ← fieldString j "kind" path with
  | "none" => pure .none
  | "address" => pure .address
  | "read_only" => pure .readOnly
  | "unrestricted" => pure .unrestricted
  | _ => throw s!"{path}: unrecognized argument capture"

def parseIndirectMode (j : Json) (path : String) : Except String IndirectModeKind := do
  match ← fieldString j "kind" path with
  | "pointer" => pure .pointer
  | "on_stack" => pure .onStack
  | "amdgpu_kernel_argument" => pure .amdgpuKernelArgument
  | _ => throw s!"{path}: unrecognized indirect argument mode"

def parseAbiAttributes (j : Json) (path : String) : Except String AbiAttributes := do
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

def parseCanonicalAbi (j : Json) (path : String) : Except String CanonicalAbi := do
  let kindNode ← parseAbiTag j path
  return {
    kind := ← canonicalAbiKind kindNode.tag
    armCall := ← (← optionalString j "arm_call" path).mapM armCallKind
    interruptKind := ← (← optionalString j "interrupt_kind" path).mapM interruptCallKind
    x86Call := ← (← optionalString j "x86_call" path).mapM x86CallKind
    payload := j
  }

def parseAbiRegisterHint (j : Json) (path : String) : Except String AbiRegisterHint := do
  match ← fieldString j "kind" path with
  | "integer" => return .integer (← integerTypeTag (← fieldString j "integer_kind" path)) (← fieldBool j "signed" path)
  | "float" => return .float (← floatTypeTag (← fieldString j "float_kind" path))
  | "pointer" => return .pointer (← fieldNat j "address_space" path)
  | _ => throw s!"{path}: unrecognized register primitive hint"

def parseAbiRegister (j : Json) (path : String) : Except String AbiRegister := do
  let kindNode ← field j "kind" path
  let kindTag ← fieldString kindNode "kind" (joinPath path "kind")
  let hintElement ← match optionalJson kindNode "hint_element" with
    | none => pure none
    | some value => pure (some (← parseAbiRegisterHint value (joinPath path "kind.hint_element")))
  return {
    kind := ← abiRegisterKind kindTag
    sizeBits := ← fieldNat j "size_bits" path
    hintElement := hintElement
    payload := j
  }

def parseAbiCastTarget (j : Json) (path : String) : Except String AbiCastTarget := do
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

def parseAbiPassMode (j : Json) (path : String) : Except String AbiPassMode := do
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
    payload := j
  }

def parseAbiArgument (j : Json) (path : String) : Except String AbiArgument := do
  let typeRef ← field j "type" path
  let typeId ← match isTypeRef typeRef with
    | some id => pure id
    | none => throw s!"{joinPath path "type"}: expected type reference"
  let layoutId ← fieldNat j "layout" path
  return {
    typeId := typeId
    layoutId := layoutId
    mode := ← parseAbiPassMode (← field j "mode" path) (joinPath path "mode")
    payload := j
  }

def parseFunctionAbi (j : Json) (path : String) : Except String FunctionAbi := do
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
    payload := j
  }

/-- Decode an exact compiler projection layout using the canonical schema. -/
def decodeCompilerLayout (j : Json) : Except String Layout :=
  parseLayout j "$.compiler_projection_layout"

/-- Decode an independently keyed compiler FnAbi query using the canonical schema. -/
def decodeCompilerFunctionAbi (j : Json) : Except String FunctionAbi :=
  parseFunctionAbi j "$.compiler_fn_abi"

def decodeCompilerValue (j : Json) : Except String TypedValue :=
  decodeValue j "$compiler_value"

end Miri.Input.DecoderValues

namespace Miri.Input
export DecoderValues (expectedMiriCommit expectedRustcCommit expectedSchema expectedSchemaVersion expectedCompilerAbiLayoutSchema decodeCompilerPredicateEvidence decodeCompilerPattern decodeTypeCompilerFacts decodeVtableEntry decodeStaticGlobalInfo validateCompilerAllocIdWorldRaw decodeCompilerLayout decodeCompilerFunctionAbi decodeCompilerValue)
end Miri.Input
