import Miri.Input.Model.Catalogs
import Miri.MIR.Syntax
import Miri.Input.JsonReader
import Miri.Input.GenericArgsCodec

namespace Miri.Input.DecodeMIR
open JsonReader

private structure TagObjectFields where
  kind : Option (String) := none

def tagObject : Parser (String) := do
  let v ← object ({} : TagObjectFields) fun v key => do
    match key with
    | "kind" => return { v with kind := some (← string) }
    | _ => skipValue; pure v
  required v.kind "kind"

def tag : Parser String := do
  if (← Std.Internal.Parsec.peek!) == '"' then string else tagObject

def mutability : Parser MIR.Mutability := do
  match ← tag with
  | "mutable" => pure .Mut
  | "immutable" => pure .Not
  | _ => fail "unknown mutability"

def safety : Parser MIR.Safety := do
  match ← tag with
  | "safe" => pure .Safe
  | "unsafe" => pure .Unsafe
  | _ => fail "unknown safety"

private structure PointerCoercionFields where
  kind : Option (String) := none
  safety : Option (MIR.Safety) := none

def pointerCoercion : Parser (MIR.PointerCoercion) := do
  let v ← object ({} : PointerCoercionFields) fun v key => do
    match key with
    | "kind" => return { v with kind := some (← string) }
    | "safety" => return { v with safety := some (← safety) }
    | _ => skipValue; pure v
  match ← required v.kind "kind" with
  | "ReifyFnPointer" => return .ReifyFnPointer (← required v.safety "safety")
  | "ClosureFnPointer" => return .ClosureFnPointer (← required v.safety "safety")
  | "UnsafeFnPointer" => pure .UnsafeFnPointer
  | "MutToConstPointer" => pure .MutToConstPointer
  | "ArrayToPointer" => pure .ArrayToPointer
  | "Unsize" => pure .Unsize
  | _ => fail "unknown pointer coercion"

def coercionSource : Parser MIR.CoercionSource := do
  match ← tag with
  | "as_cast" => pure .AsCast
  | "implicit" => pure .Implicit
  | _ => fail "unknown coercionSource"

private structure CastKindFields where
  kind : Option (String) := none
  coercion : Option (MIR.PointerCoercion) := none
  source : Option (MIR.CoercionSource) := none

def castKind : Parser (MIR.CastKind) := do
  let v ← object ({} : CastKindFields) fun v key => do
    match key with
    | "kind" => return { v with kind := some (← string) }
    | "coercion" => return { v with coercion := some (← pointerCoercion) }
    | "source" => return { v with source := some (← coercionSource) }
    | _ => skipValue; pure v
  match ← required v.kind "kind" with
  | "PointerExposeProvenance" => pure .PointerExposeProvenance
  | "PointerWithExposedProvenance" => pure .PointerWithExposedProvenance
  | "IntToInt" => pure .IntToInt
  | "FloatToInt" => pure .FloatToInt
  | "FloatToFloat" => pure .FloatToFloat
  | "IntToFloat" => pure .IntToFloat
  | "PtrToPtr" => pure .PtrToPtr
  | "FnPtrToPtr" => pure .FnPtrToPtr
  | "Transmute" => pure .Transmute
  | "BoxDerefTransmute" => pure .BoxDerefTransmute
  | "Subtype" => pure .Subtype
  | "PointerCoercion" => return .PointerCoercion (← required v.coercion "coercion") (← required v.source "source")
  | _ => fail "unknown cast kind"

private structure BorrowFields where
  kind : Option (String) := none
  retag_mode : Option (String) := none
  fake_kind : Option (String) := none
  mutability_kind : Option (String) := none

def borrow : Parser (MIR.BorrowKind) := do
  let v ← object ({} : BorrowFields) fun v key => do
    match key with
    | "kind" => return { v with kind := some (← string) }
    | "retag_mode" => return { v with retag_mode := some (← tag) }
    | "fake_kind" => return { v with fake_kind := some (← tag) }
    | "mutability_kind" => return { v with mutability_kind := some (← tag) }
    | _ => skipValue; pure v
  match ← required v.kind "kind" with
  | "shared" => pure .Shared
  | "fake" =>
    unless (← required v.retag_mode "retag_mode") == "default" do fail "unknown fake-borrow retag mode"
    match ← required v.fake_kind "fake_kind" with
    | "shallow" => pure (.Fake .Shallow)
    | "deep" => pure (.Fake .Deep)
    | _ => fail "unknown fake borrow"
  | "mutable" =>
    match ← required v.mutability_kind "mutability_kind" with
    | "default" => pure (.Mut .Default)
    | "two_phase" => pure (.Mut .TwoPhaseBorrow)
    | "closure_capture" => pure (.Mut .ClosureCapture)
    | _ => fail "unknown mutable borrow"
  | _ => fail "unknown borrow kind"

private structure ProjectionFields where
  kind : Option (String) := none
  index : Option (Nat) := none
  field_type : Option (Nat) := none
  «local» : Option (Nat) := none
  offset : Option (Nat) := none
  min_length : Option (Nat) := none
  «from» : Option (Nat) := none
  to : Option (Nat) := none
  variant_index : Option (Nat) := none
  cast_type : Option (Nat) := none
  inner_type : Option (Nat) := none
  resulting_type : Option (Nat) := none
  from_end : Option (Bool) := none
  name : Option (Option String) := none

def projection : Parser (MIR.ProjectionElem × Nat) := do
  let v ← object ({} : ProjectionFields) fun v key => do
    match key with
    | "kind" => return { v with kind := some (← string) }
    | "index" => return { v with index := some (← natural) }
    | "field_type" => return { v with field_type := some (← natural) }
    | "local" => return { v with «local» := some (← natural) }
    | "offset" => return { v with offset := some (← natural) }
    | "min_length" => return { v with min_length := some (← natural) }
    | "from" => return { v with «from» := some (← natural) }
    | "to" => return { v with to := some (← natural) }
    | "variant_index" => return { v with variant_index := some (← natural) }
    | "cast_type" => return { v with cast_type := some (← natural) }
    | "inner_type" => return { v with inner_type := some (← natural) }
    | "resulting_type" => return { v with resulting_type := some (← natural) }
    | "from_end" => return { v with from_end := some (← boolean) }
    | "name" => return { v with name := some (← nullable string) }
    | _ => skipValue; pure v
  let value ← (show Parser MIR.ProjectionElem from do
    match ← required v.kind "kind" with
    | "Deref" => pure MIR.ProjectionElem.Deref
    | "Field" => return .Field (← required v.index "index") (← required v.field_type "field_type")
    | "Index" => return .Index (← required v.«local» "local")
    | "ConstantIndex" => return .ConstantIndex (← required v.offset "offset") (← required v.min_length "min_length") (← required v.from_end "from_end")
    | "Subslice" => return .Subslice (← required v.«from» "from") (← required v.to "to") (← required v.from_end "from_end")
    | "Downcast" => return .Downcast (← required v.name "name") (← required v.variant_index "variant_index")
    | "OpaqueCast" => return .OpaqueCast (← required v.cast_type "cast_type")
    | "UnwrapUnsafeBinder" => return .UnwrapUnsafeBinder (← required v.inner_type "inner_type")
    | "PhantomDeref" => pure .PhantomDeref
    | _ => fail "unknown projection")
  return (value, (← required v.resulting_type "resulting_type"))

/-- Local metadata is consumed as soon as its containing MIR node is built. -/
structure ParsedPlace where
  value : MIR.Place
  typeId : Nat
  projectionTypes : Array Nat

instance : Coe ParsedPlace MIR.Place := ⟨(·.value)⟩

private structure PlaceFields where
  «local» : Option (Nat) := none
  type : Option (Nat) := none
  projection : Option (Array (MIR.ProjectionElem × Nat)) := none

def place : Parser (ParsedPlace) := do
  let v ← object ({} : PlaceFields) fun v key => do
    match key with
    | "local" => return { v with «local» := some (← natural) }
    | "type" => return { v with type := some (← natural) }
    | "projection" => return { v with projection := some (← array projection) }
    | _ => skipValue; pure v
  let projections ← required v.projection "projection"
  return ⟨⟨(← required v.«local» "local"), projections.map Prod.fst⟩,
    (← required v.type "type"), projections.map Prod.snd⟩

def binOp : Parser MIR.BinOp := do
  match ← tag with
  | "add" => pure .Add
  | "add_unchecked" => pure .AddUnchecked
  | "add_with_overflow" => pure .AddWithOverflow
  | "sub" => pure .Sub
  | "sub_unchecked" => pure .SubUnchecked
  | "sub_with_overflow" => pure .SubWithOverflow
  | "mul" => pure .Mul
  | "mul_unchecked" => pure .MulUnchecked
  | "mul_with_overflow" => pure .MulWithOverflow
  | "div" => pure .Div
  | "rem" => pure .Rem
  | "bit_xor" => pure .BitXor
  | "bit_and" => pure .BitAnd
  | "bit_or" => pure .BitOr
  | "shift_left" => pure .Shl
  | "shift_left_unchecked" => pure .ShlUnchecked
  | "shift_right" => pure .Shr
  | "shift_right_unchecked" => pure .ShrUnchecked
  | "equal" => pure .Eq
  | "less_than" => pure .Lt
  | "less_equal" => pure .Le
  | "not_equal" => pure .Ne
  | "greater_equal" => pure .Ge
  | "greater_than" => pure .Gt
  | "compare" => pure .Cmp
  | "pointer_offset" => pure .Offset
  | _ => fail "unknown binOp"

def unOp : Parser MIR.UnOp := do
  match ← tag with
  | "not" => pure .Not
  | "negate" => pure .Neg
  | "pointer_metadata" => pure .PtrMetadata
  | _ => fail "unknown unOp"

def variance : Parser MIR.Variance := do
  match ← tag with
  | "covariant" => pure .Covariant
  | "contravariant" => pure .Contravariant
  | "invariant" => pure .Invariant
  | "bivariant" => pure .Bivariant
  | _ => fail "unknown variance"

def unwindReason : Parser MIR.UnwindTerminateReason := do
  match ← tag with
  | "abi" => pure .Abi
  | "in_cleanup" => pure .InCleanup
  | _ => fail "unknown unwindReason"

def callSource : Parser MIR.CallSource := do
  match ← tag with
  | "overloaded_operator" => pure .OverloadedOperator
  | "match_comparison" => pure .MatchCmp
  | "miscellaneous_desugaring" => pure .Misc
  | "clone_or_use" => pure .Use
  | "normal_call" => pure .Normal
  | _ => fail "unknown callSource"

def asmArch : Parser MIR.InlineAsmArch := do
  match ← string with
  | "X86" => pure .X86
  | "X86_64" => pure .X86_64
  | "Arm" => pure .Arm
  | "Arm64EC" => pure .Arm64EC
  | "AArch64" => pure .AArch64
  | "Amdgpu" => pure .Amdgpu
  | "RiscV32" => pure .RiscV32
  | "RiscV64" => pure .RiscV64
  | "Nvptx64" => pure .Nvptx64
  | "PowerPC" => pure .PowerPC
  | "PowerPC64" => pure .PowerPC64
  | "Hexagon" => pure .Hexagon
  | "LoongArch32" => pure .LoongArch32
  | "LoongArch64" => pure .LoongArch64
  | "Mips" => pure .Mips
  | "Mips64" => pure .Mips64
  | "Xtensa" => pure .Xtensa
  | "S390x" => pure .S390x
  | "Sparc" => pure .Sparc
  | "Sparc64" => pure .Sparc64
  | "SpirV" => pure .SpirV
  | "Wasm32" => pure .Wasm32
  | "Wasm64" => pure .Wasm64
  | "Bpf" => pure .Bpf
  | "Avr" => pure .Avr
  | "Msp430" => pure .Msp430
  | "M68k" => pure .M68k
  | "CSKY" => pure .CSky
  | _ => fail "unknown asmArch"

private structure AnnotationObjectFields where
  index : Option (Nat) := none

def annotationObject : Parser (Nat) := do
  let v ← object ({} : AnnotationObjectFields) fun v key => do
    match key with
    | "index" => return { v with index := some (← natural) }
    | _ => skipValue; pure v
  required v.index "index"

def annotation : Parser Nat := do
  if (← Std.Internal.Parsec.peek!) == '{' then annotationObject else natural

private structure AggregateFields where
  kind : Option (String) := none
  element_type : Option (Nat) := none
  def_id : Option (Nat) := none
  variant_index : Option (Nat) := none
  generic_args : Option (Array MIR.GenericArg) := none
  user_type_annotation : Option (Option Nat) := none
  active_union_field : Option (Option Nat) := none
  pointee_type : Option (Nat) := none
  mutability : Option (MIR.Mutability) := none

def aggregate : Parser (MIR.AggregateKind) := do
  let v ← object ({} : AggregateFields) fun v key => do
    match key with
    | "kind" => return { v with kind := some (← string) }
    | "element_type" => return { v with element_type := some (← natural) }
    | "def_id" => return { v with def_id := some (← natural) }
    | "variant_index" => return { v with variant_index := some (← natural) }
    | "generic_args" => return { v with generic_args := some (← GenericArgsCodec.decode) }
    | "user_type_annotation" => return { v with user_type_annotation := some (← nullable annotation) }
    | "active_union_field" => return { v with active_union_field := some (← nullable natural) }
    | "pointee_type" => return { v with pointee_type := some (← natural) }
    | "mutability" => return { v with mutability := some (← mutability) }
    | _ => skipValue; pure v
  match ← required v.kind "kind" with
  | "Array" => return .Array (← required v.element_type "element_type")
  | "Tuple" => pure .Tuple
  | "Adt" => return .Adt (← required v.def_id "def_id") (← required v.variant_index "variant_index") (← required v.generic_args "generic_args") (← required v.user_type_annotation "user_type_annotation") (← required v.active_union_field "active_union_field")
  | "Closure" => return .Closure (← required v.def_id "def_id") (← required v.generic_args "generic_args")
  | "Coroutine" => return .Coroutine (← required v.def_id "def_id") (← required v.generic_args "generic_args")
  | "CoroutineClosure" => return .CoroutineClosure (← required v.def_id "def_id") (← required v.generic_args "generic_args")
  | "RawPtr" => return .RawPtr (← required v.pointee_type "pointee_type") (← required v.mutability "mutability")
  | _ => fail "unknown aggregate kind"

private structure FakeReadFields where
  kind : Option (String) := none
  hoisted_from : Option (Option Nat) := none

def fakeRead : Parser (MIR.FakeReadCause) := do
  let v ← object ({} : FakeReadFields) fun v key => do
    match key with
    | "kind" => return { v with kind := some (← string) }
    | "hoisted_from" => return { v with hoisted_from := some (← nullable natural) }
    | _ => skipValue; pure v
  match ← required v.kind "kind" with
  | "match_guard" => pure .ForMatchGuard
  | "matched_place" => return .ForMatchedPlace (← required v.hoisted_from "hoisted_from")
  | "guard_binding" => pure .ForGuardBinding
  | "let_binding" => return .ForLet (← required v.hoisted_from "hoisted_from")
  | "index" => pure .ForIndex
  | _ => fail "unknown fake read cause"

private structure UserProjectionKindFields where
  kind : Option (String) := none
  index : Option (Nat) := none
  offset : Option (Nat) := none
  min_length : Option (Nat) := none
  «from» : Option (Nat) := none
  to : Option (Nat) := none
  variant_index : Option (Nat) := none
  from_end : Option (Bool) := none
  name : Option (Option String) := none

def userProjectionKind : Parser (MIR.ProjectionKind) := do
  let v ← object ({} : UserProjectionKindFields) fun v key => do
    match key with
    | "kind" => return { v with kind := some (← string) }
    | "index" => return { v with index := some (← natural) }
    | "offset" => return { v with offset := some (← natural) }
    | "min_length" => return { v with min_length := some (← natural) }
    | "from" => return { v with «from» := some (← natural) }
    | "to" => return { v with to := some (← natural) }
    | "variant_index" => return { v with variant_index := some (← natural) }
    | "from_end" => return { v with from_end := some (← boolean) }
    | "name" => return { v with name := some (← nullable string) }
    | _ => skipValue; pure v
  match ← required v.kind "kind" with
  | "Deref" => pure .Deref
  | "Field" => return .Field (← required v.index "index")
  | "Index" => pure .Index
  | "ConstantIndex" => return .ConstantIndex (← required v.offset "offset") (← required v.min_length "min_length") (← required v.from_end "from_end")
  | "Subslice" => return .Subslice (← required v.«from» "from") (← required v.to "to") (← required v.from_end "from_end")
  | "Downcast" => return .Downcast (← required v.name "name") (← required v.variant_index "variant_index")
  | "OpaqueCast" => pure .OpaqueCast
  | "UnwrapUnsafeBinder" => pure .UnwrapUnsafeBinder
  | "PhantomDeref" => pure .PhantomDeref
  | _ => fail "unknown user projection"

private structure UserProjectionFields where
  base_index : Option (Nat) := none
  projections : Option (Array MIR.ProjectionKind) := none

def userProjection : Parser (MIR.UserTypeProjection) := do
  let v ← object ({} : UserProjectionFields) fun v key => do
    match key with
    | "base_index" => return { v with base_index := some (← natural) }
    | "projections" => return { v with projections := some (← array userProjectionKind) }
    | _ => skipValue; pure v
  return ⟨(← required v.base_index "base_index"), (← required v.projections "projections")⟩

def coveragePointKind : Parser MIR.CoveragePointKind := do
  match ← tag with
  | "expr" => pure .Expr
  | "implicit_else" => pure .ImplicitElse
  | "function_end" => pure .FunctionEnd
  | _ => fail "unknown coveragePointKind"

private structure HirIdFields where
  owner_def_id : Option (Nat) := none
  local_id : Option (Nat) := none

def hirId : Parser (MIR.HirId) := do
  let v ← object ({} : HirIdFields) fun v key => do
    match key with
    | "owner_def_id" => return { v with owner_def_id := some (← natural) }
    | "local_id" => return { v with local_id := some (← natural) }
    | _ => skipValue; pure v
  return ⟨(← required v.owner_def_id "owner_def_id"), (← required v.local_id "local_id")⟩

private structure CoverageFields where
  kind : Option (String) := none
  point_kind : Option (MIR.CoveragePointKind) := none
  hir_id : Option (MIR.HirId) := none
  id : Option (Nat) := none
  bcb : Option (Nat) := none

def coverage : Parser (MIR.CoverageKind) := do
  let v ← object ({} : CoverageFields) fun v key => do
    match key with
    | "kind" => return { v with kind := some (← string) }
    | "point_kind" => return { v with point_kind := some (← coveragePointKind) }
    | "hir_id" => return { v with hir_id := some (← hirId) }
    | "id" => return { v with id := some (← natural) }
    | "bcb" => return { v with bcb := some (← natural) }
    | _ => skipValue; pure v
  match ← required v.kind "kind" with
  | "point" => return .Point (← required v.point_kind "point_kind") (← required v.hir_id "hir_id")
  | "block_marker" => return .BlockMarker (← required v.id "id")
  | "virtual_counter" => return .VirtualCounter (← required v.bcb "bcb")
  | _ => fail "unknown coverage kind"

private structure CoroutineFields where
  kind : Option (String) := none
  desugaring : Option (String) := none
  source : Option (String) := none
  movability : Option (String) := none

def coroutine : Parser (MIR.CoroutineKind) := do
  let v ← object ({} : CoroutineFields) fun v key => do
    match key with
    | "kind" => return { v with kind := some (← string) }
    | "desugaring" => return { v with desugaring := some (← string) }
    | "source" => return { v with source := some (← string) }
    | "movability" => return { v with movability := some (← string) }
    | _ => skipValue; pure v
  match ← required v.kind "kind" with
  | "desugared" =>
    let desugaring ← match (← required v.desugaring "desugaring") with
      | "async" => pure MIR.CoroutineDesugaring.Async
      | "gen" => pure .Gen
      | "async_gen" => pure .AsyncGen
      | _ => fail "unknown coroutine desugaring"
    let source ← match (← required v.source "source") with
      | "block" => pure MIR.CoroutineSource.Block
      | "closure" => pure .Closure
      | "function" => pure .Fn
      | _ => fail "unknown coroutine source"
    return .Desugared desugaring source
  | "coroutine" =>
    match (← required v.movability "movability") with
    | "static" => pure (.Coroutine .Static)
    | "movable" => pure (.Coroutine .Movable)
    | _ => fail "unknown coroutine movability"
  | _ => fail "unknown coroutine kind"

private structure UnwindFields where
  kind : Option (String) := none
  target : Option (Nat) := none
  reason : Option (MIR.UnwindTerminateReason) := none

def unwind : Parser (MIR.UnwindAction) := do
  let v ← object ({} : UnwindFields) fun v key => do
    match key with
    | "kind" => return { v with kind := some (← string) }
    | "target" => return { v with target := some (← natural) }
    | "reason" => return { v with reason := some (← unwindReason) }
    | _ => skipValue; pure v
  match ← required v.kind "kind" with
  | "Continue" => pure .Continue
  | "Unreachable" => pure .Unreachable
  | "Cleanup" => return .Cleanup (← required v.target "target")
  | "Terminate" => return .Terminate (← required v.reason "reason")
  | _ => fail "unknown unwind action"

private structure LoopHintFields where
  kind : Option (String) := none
  count : Option (Nat) := none

def loopHint : Parser (MIR.LoopHintAttr) := do
  let v ← object ({} : LoopHintFields) fun v key => do
    match key with
    | "kind" => return { v with kind := some (← string) }
    | "count" => return { v with count := some (← natural) }
    | _ => skipValue; pure v
  match ← required v.kind "kind" with
  | "Hint" => pure .Hint
  | "Full" => pure .Full
  | "Never" => pure .Never
  | "Count" => return .Count (← required v.count "count")
  | _ => fail "unknown loop hint"

private structure AsmRegisterFields where
  kind : Option (String) := none
  arch : Option (MIR.InlineAsmArch) := none
  name : Option (String) := none

def asmRegister : Parser (MIR.InlineAsmRegOrRegClass) := do
  let v ← object ({} : AsmRegisterFields) fun v key => do
    match key with
    | "kind" => return { v with kind := some (← string) }
    | "arch" => return { v with arch := some (← asmArch) }
    | "name" => return { v with name := some (← string) }
    | _ => skipValue; pure v
  match ← required v.kind "kind" with
  | "register" => return .Reg (← required v.arch "arch") (← required v.name "name")
  | "register_class" => return .RegClass (← required v.arch "arch") (← required v.name "name")
  | _ => fail "unknown assembly register kind"

def character : Parser Char := do
  match (← string).toList with
  | [c] => pure c
  | _ => fail "assembly modifier must be one character"

private structure AsmPieceFields where
  kind : Option (String) := none
  text : Option (String) := none
  operand_index : Option (Nat) := none
  modifier : Option (Option Char) := none
  span : Option (Nat) := none

def asmPiece : Parser (MIR.InlineAsmTemplatePiece) := do
  let v ← object ({} : AsmPieceFields) fun v key => do
    match key with
    | "kind" => return { v with kind := some (← string) }
    | "text" => return { v with text := some (← string) }
    | "operand_index" => return { v with operand_index := some (← natural) }
    | "modifier" => return { v with modifier := some (← nullable character) }
    | "span" => return { v with span := some (← natural) }
    | _ => skipValue; pure v
  match ← required v.kind "kind" with
  | "string" => return .String (← required v.text "text")
  | "placeholder" => return .Placeholder (← required v.operand_index "operand_index") (← required v.modifier "modifier") ⟨(← required v.span "span")⟩
  | _ => fail "unknown assembly template piece"

private structure PhaseFields where
  kind : Option (String) := none
  phase : Option (String) := none

def phase : Parser (MIR.MirPhase) := do
  let v ← object ({} : PhaseFields) fun v key => do
    match key with
    | "kind" => return { v with kind := some (← string) }
    | "phase" => return { v with phase := some (← tag) }
    | _ => skipValue; pure v
  match ← required v.kind "kind" with
  | "built" =>
    unless v.phase.isNone do fail "built MIR phase has a subphase"
    pure .Built
  | "analysis" =>
    match (← required v.phase "phase") with
    | "initial" => pure (.Analysis .Initial)
    | "post_cleanup" => pure (.Analysis .PostCleanup)
    | _ => fail "unknown analysis phase"
  | "runtime" =>
    match (← required v.phase "phase") with
    | "initial" => pure (.Runtime .Initial)
    | "post_cleanup" => pure (.Runtime .PostCleanup)
    | "optimized" => pure (.Runtime .Optimized)
    | _ => fail "unknown runtime phase"
  | _ => fail "unknown MIR phase"

private structure SourceFields where
  span : Option (Nat) := none
  scope : Option (Nat) := none

def source : Parser (MIR.SourceInfo) := do
  let v ← object ({} : SourceFields) fun v key => do
    match key with
    | "span" => return { v with span := some (← natural) }
    | "scope" => return { v with scope := some (← natural) }
    | _ => skipValue; pure v
  return ⟨⟨(← required v.span "span")⟩, (← required v.scope "scope")⟩

def sourceInfo : Parser Miri.Input.SourceInfo := do
  let value ← source
  return ⟨value.span.id, value.scope⟩

private structure InlinedScopeFields where
  instance_id : Option (Nat) := none
  callsite_span : Option (Nat) := none
  requires_caller_location : Option (Bool) := none

def inlinedScope : Parser (InlinedScope) := do
  let v ← object ({} : InlinedScopeFields) fun v key => do
    match key with
    | "instance_id" => return { v with instance_id := some (← natural) }
    | "callsite_span" => return { v with callsite_span := some (← natural) }
    | "requires_caller_location" => return { v with requires_caller_location := some (← boolean) }
    | _ => skipValue; pure v
  return { instanceId := (← required v.instance_id "instance_id"), callsiteSpanId := (← required v.callsite_span "callsite_span"), requiresCallerLocation := (← required v.requires_caller_location "requires_caller_location") }

private structure ScopeFields where
  scope : Option (Nat) := none
  span : Option (Nat) := none
  parent : Option (Option Nat) := none
  inlined_parent_scope : Option (Option Nat) := none
  inlined : Option (Option InlinedScope) := none

def scope : Parser (SourceScope) := do
  let v ← object ({} : ScopeFields) fun v key => do
    match key with
    | "scope" => return { v with scope := some (← natural) }
    | "span" => return { v with span := some (← natural) }
    | "parent" => return { v with parent := some (← nullable natural) }
    | "inlined_parent_scope" => return { v with inlined_parent_scope := some (← nullable natural) }
    | "inlined" => return { v with inlined := some (← nullable inlinedScope) }
    | _ => skipValue; pure v
  return { id := (← required v.scope "scope"), spanId := (← required v.span "span"), parent := v.parent.join, inlinedParent := v.inlined_parent_scope.join, inlined := v.inlined.join }

private structure BacktracePositionFields where
  byte_position : Option (Nat) := none
  line : Option (Nat) := none
  zero_based_char_column : Option (Nat) := none
  filename : Option (Nat) := none

def backtracePosition : Parser (CompilerSourcePosition) := do
  let v ← object ({} : BacktracePositionFields) fun v key => do
    match key with
    | "byte_position" => return { v with byte_position := some (← natural) }
    | "line" => return { v with line := some (← natural) }
    | "zero_based_char_column" => return { v with zero_based_char_column := some (← natural) }
    | "filename" => return { v with filename := some (← natural) }
    | _ => skipValue; pure v
  return { bytePosition := (← required v.byte_position "byte_position"), line := (← required v.line "line"), column := (← required v.zero_based_char_column "zero_based_char_column"), filename := (← required v.filename "filename") }

private structure BacktraceFields where
  span : Option (Nat) := none
  source_position : Option (CompilerSourcePosition) := none

def backtrace (path : String) : Parser (BacktraceSpan) := do
  let v ← object ({} : BacktraceFields) fun v key => do
    match key with
    | "span" => return { v with span := some (← natural) }
    | "source_position" => return { v with source_position := some (← backtracePosition) }
    | _ => skipValue; pure v
  let spanId ← required v.span "span"
  let position ← required v.source_position "source_position"
  unless position.bytePosition < 2^32 do fail s!"{path}: compiler BytePos exceeds u32"
  return { spanId, position }

private structure CallEvidenceFields where
  kind : Option (String) := none
  instance_id : Option (Option Nat) := none
  function_type : Option (Nat) := none
  dispatch_slot : Option (Option Nat) := none
  fn_abi : Option (Nat) := none

def callEvidence : Parser (CallResolutionEvidence) := do
  let v ← object ({} : CallEvidenceFields) fun v key => do
    match key with
    | "kind" => return { v with kind := some (← string) }
    | "instance_id" => return { v with instance_id := some (← nullable natural) }
    | "function_type" => return { v with function_type := some (← natural) }
    | "dispatch_slot" => return { v with dispatch_slot := some (← nullable natural) }
    | "fn_abi" => return { v with fn_abi := some (← natural) }
    | _ => skipValue; pure v
  let kind ← match (← required v.kind "kind") with
    | "llvm_intrinsic" => pure CallResolutionKind.llvmIntrinsic
    | "resolved_instance" | "source_instance" => pure CallResolutionKind.direct
    | "virtual_dispatch" => pure .virtualDispatch
    | "indirect_function_pointer" | "source_function_pointer" => pure .indirect
    | _ => fail "unknown call resolution"
  let instanceId ← if kind == .indirect then pure none else some <$> (required (← required v.instance_id "instance_id") "non-null instance_id")
  let dispatchSlot ← if kind == .virtualDispatch then some <$> (required (← required v.dispatch_slot "dispatch_slot") "non-null dispatch_slot") else pure none
  let abi ← if v.kind == some "source_instance" || v.kind == some "source_function_pointer" then do
      unless v.fn_abi.isNone && v.dispatch_slot.isNone do
        fail "raw source instance must not carry physical ABI or dispatch-slot evidence"
      pure CallAbiEvidence.sourceSignature
    else if kind == .llvmIntrinsic then do
      unless v.fn_abi.isNone do fail "LLVM intrinsic must not carry an ordinary fn_abi"
      unless v.dispatch_slot.isNone do fail "LLVM intrinsic must not carry a dispatch slot"
      pure CallAbiEvidence.llvmIntrinsic
    else pure (.normal (← required v.fn_abi "fn_abi"))
  return { kind, instanceId, dispatchSlot, functionType := some (← required v.function_type "function_type"), abi }

private structure SupertraitQueryFields where
  query_kind : Option (String) := none
  typing_env : Option (String) := none
  input_source : Option (Nat) := none
  input_target : Option (Nat) := none

def supertraitQuery : Parser (Nat × Nat) := do
  let v ← object ({} : SupertraitQueryFields) fun v key => do
    match key with
    | "query_kind" => return { v with query_kind := some (← string) }
    | "typing_env" => return { v with typing_env := some (← string) }
    | "input_source" => return { v with input_source := some (← natural) }
    | "input_target" => return { v with input_target := some (← natural) }
    | _ => skipValue; pure v
  unless (← required v.query_kind "query_kind") == "supertrait_slot" && (← required v.typing_env "typing_env") == "fully_monomorphized" do
    fail "invalid dynamic vtable query metadata"
  return ((← required v.input_source "input_source"), (← required v.input_target "input_target"))

private structure UpcastDescriptorFields where
  kind : Option (String) := none
  runtime_vtable : Option (String) := none
  supertrait_slot_query : Option (Nat × Nat) := none
  source_type : Option (Nat) := none
  target_type : Option (Nat) := none
  source_pointee_type : Option (Nat) := none
  target_pointee_type : Option (Nat) := none
  source_tail_type : Option (Nat) := none
  target_tail_type : Option (Nat) := none

def upcastDescriptor : Parser (Option DynamicUpcastEvidence) := do
  let v ← object ({} : UpcastDescriptorFields) fun v key => do
    match key with
    | "kind" => return { v with kind := some (← string) }
    | "runtime_vtable" => return { v with runtime_vtable := some (← string) }
    | "supertrait_slot_query" => return { v with supertrait_slot_query := some (← supertraitQuery) }
    | "source_type" => return { v with source_type := some (← natural) }
    | "target_type" => return { v with target_type := some (← natural) }
    | "source_pointee_type" => return { v with source_pointee_type := some (← natural) }
    | "target_pointee_type" => return { v with target_pointee_type := some (← natural) }
    | "source_tail_type" => return { v with source_tail_type := some (← natural) }
    | "target_tail_type" => return { v with target_tail_type := some (← natural) }
    | _ => skipValue; pure v
  let kind ← required v.kind "kind"
  if kind != "dynamic_vtable_upcast" then return none
  unless (← required v.runtime_vtable "runtime_vtable") == "source_operand_metadata" do fail "invalid dynamic vtable query metadata"
  let query ← required v.supertrait_slot_query "supertrait_slot_query"
  return some {
    operandType := 0, castTarget := 0, sourceType := (← required v.source_type "source_type"),
    targetType := (← required v.target_type "target_type"), sourcePointeeType := (← required v.source_pointee_type "source_pointee_type"),
    targetPointeeType := (← required v.target_pointee_type "target_pointee_type"), sourceTailType := (← required v.source_tail_type "source_tail_type"),
    targetTailType := (← required v.target_tail_type "target_tail_type"), querySource := query.1, queryTarget := query.2 }

def upcast : Parser (Option DynamicUpcastEvidence) := do
  return (← nullable upcastDescriptor).join

end Miri.Input.DecodeMIR
