import Miri.Input.JsonReader
import Miri.Input.DraftMIR
import Miri.Input.MIRLeaves
import Miri.Input.DecoderValues

namespace Miri.Input.DecodeMIR
open JsonReader Miri.MIR
open Std.Internal.Parsec Std.Internal.Parsec.String
abbrev Result := Except String
private def reject (message : String) : JsonReader.Parser (α) := liftExcept (.error message)


/-- Reject fields belonging to a different known constructor. Unknown extension
fields are skipped while parsing and do not enter these schema accumulators. -/
private def rejectIncompatible (allowed : List String) (fields : List (String × Bool)) : JsonReader.Parser Unit := do
  for (name, present) in fields do
    if present && !allowed.contains name then
      reject s!"field `{name}` is incompatible with the selected variant"

private def number : JsonReader.Parser (Nat) := do
  if (← peek!) == '"' then
    let s ← string
    match s.toNat? with
    | some n => pure n
    | none => reject "invalid decimal integer"
  else natural

structure ConstValueFields where
  kind : Option (String) := none
  bits_unsigned : Option (Nat) := none
  allocation : Option (Nat) := none
  offset_bytes : Option (Nat) := none
  immutable : Option (Bool) := none
  shared_ref : Option (Bool) := none
  address : Option (Nat) := none
  address_width_bytes : Option (Nat) := none
  metadata_length : Option (Nat) := none

def parseConstValueField (s : ConstValueFields) (key : String) : JsonReader.Parser (ConstValueFields) := do
  match key with
  | "kind" => return {s with kind := some (← string)}
  | "bits_unsigned" => return {s with bits_unsigned := some (← number)}
  | "allocation" => return {s with allocation := some (← natural)}
  | "offset_bytes" => return {s with offset_bytes := some (← natural)}
  | "immutable" => return {s with immutable := some (← boolean)}
  | "shared_ref" => return {s with shared_ref := some (← boolean)}
  | "address" => return {s with address := some (← number)}
  | "address_width_bytes" => return {s with address_width_bytes := some (← natural)}
  | "metadata_length" => return {s with metadata_length := some (← natural)}
  | _ => skipValue; pure s
def finishConstValueFields (s : ConstValueFields) : JsonReader.Parser (DraftConstValue) := do
  let discriminator ← required s.kind "kind"
  let allowed : List String := match discriminator with
    | "zero_sized" => ["kind"]
    | "scalar" => ["kind", "bits_unsigned"]
    | "pointer_scalar" => ["kind", "allocation", "offset_bytes", "immutable", "shared_ref"]
    | "pointer_scalar_without_provenance" => ["kind", "address", "address_width_bytes"]
    | "slice_allocation" => ["kind", "allocation", "metadata_length"]
    | "indirect_allocation" => ["kind", "allocation", "offset_bytes"]
    | _ => ["kind"]
  rejectIncompatible allowed [("kind", s.kind.isSome), ("bits_unsigned", s.bits_unsigned.isSome), ("allocation", s.allocation.isSome), ("offset_bytes", s.offset_bytes.isSome), ("immutable", s.immutable.isSome), ("shared_ref", s.shared_ref.isSome), ("address", s.address.isSome), ("address_width_bytes", s.address_width_bytes.isSome), ("metadata_length", s.metadata_length.isSome)]
  match (← required s.kind "kind") with
  | "zero_sized" => pure (.ready .ZeroSized)
  | "scalar" => pure (.scalar (← required s.bits_unsigned "bits_unsigned"))
  | "pointer_scalar" => pure (.ready (.Scalar (.Ptr (.Allocation (← required s.allocation "allocation") (← required s.offset_bytes "offset_bytes") (← required s.immutable "immutable") (← required s.shared_ref "shared_ref")))))
  | "pointer_scalar_without_provenance" => pure (.ready (.Scalar (.Ptr (.Address (← required s.address "address") (← required s.address_width_bytes "address_width_bytes")))))
  | "slice_allocation" => pure (.ready (.Slice (← required s.allocation "allocation") (← required s.metadata_length "metadata_length")))
  | "indirect_allocation" => pure (.ready (.Indirect (← required s.allocation "allocation") (← required s.offset_bytes "offset_bytes")))
  | _ => reject "unknown or unavailable evaluated constant"
def parseConstValue : JsonReader.Parser (DraftConstValue) := do
  finishConstValueFields (← object {} parseConstValueField)
structure ParseEvaluatedFields where
  kind : Option (String) := none
  value : Option (DraftConstValue) := none

def parseEvaluatedField (s : ParseEvaluatedFields) (key : String) : JsonReader.Parser (ParseEvaluatedFields) := do
  match key with
  | "kind" => return {s with kind := some (← string)}
  | "value" => return {s with value := some (← parseConstValue)}
  | _ => skipValue; pure s
def finishParseEvaluatedFields (s : ParseEvaluatedFields) : JsonReader.Parser (DraftConstValue) := do
  unless (← required s.kind "kind") == "evaluated_const" do reject "unknown constant evaluation record"
  required s.value "value"
def parseEvaluated : JsonReader.Parser (DraftConstValue) := do
  finishParseEvaluatedFields (← object {} parseEvaluatedField)
structure ParseConstOperandFields where
  type : Option (Nat) := none
  span : Option (Nat) := none
  user_type_annotation : Option (Option Nat) := none
  constant : Option (DraftConstValue) := none

def parseConstOperandField (s : ParseConstOperandFields) (key : String) : JsonReader.Parser (ParseConstOperandFields) := do
  match key with
  | "type" => return {s with type := some (← natural)}
  | "span" => return {s with span := some (← natural)}
  | "user_type_annotation" => return {s with user_type_annotation := some (← nullable annotation)}
  | "constant" => return {s with constant := some (← parseEvaluated)}
  | _ => skipValue; pure s
def finishParseConstOperandFields (s : ParseConstOperandFields) : JsonReader.Parser (DraftConstant) := do
  let pair ← required s.constant "constant"
  return ⟨(← required s.type "type"), ⟨(← required s.span "span")⟩, (← required s.user_type_annotation "user_type_annotation"), pair⟩
def parseConstOperand : JsonReader.Parser (DraftConstant) := do
  finishParseConstOperandFields (← object {} parseConstOperandField)
structure RuntimeCheckFields where
  kind : Option (String) := none
  enabled : Option (Bool) := none

def runtimeCheckField (s : RuntimeCheckFields) (key : String) : JsonReader.Parser (RuntimeCheckFields) := do
  match key with
  | "kind" => return {s with kind := some (← string)}
  | "enabled" => return {s with enabled := some (← boolean)}
  | _ => skipValue; pure s
def finishRuntimeCheckFields (s : RuntimeCheckFields) : JsonReader.Parser (MIR.RuntimeChecks) := do
  let _ ← required s.enabled "enabled"
  match (← required s.kind "kind") with
  | "ub_checks" => pure .UbChecks
  | "contract_checks" => pure .ContractChecks
  | "overflow_checks" => pure .OverflowChecks
  | _ => reject "unknown runtime check"
def runtimeCheck : JsonReader.Parser (MIR.RuntimeChecks) := do
  finishRuntimeCheckFields (← object {} runtimeCheckField)
structure OperandFields where
  kind : Option (String) := none
  place : Option (Draft.Place) := none
  constant : Option (DraftConstant) := none
  check : Option (MIR.RuntimeChecks) := none

def operandField (s : OperandFields) (key : String) : JsonReader.Parser (OperandFields) := do
  match key with
  | "kind" => return {s with kind := some (← string)}
  | "place" => return {s with place := some (← place)}
  | "constant" => return {s with constant := some (← parseConstOperand)}
  | "check" => return {s with check := some (← runtimeCheck)}
  | _ => skipValue; pure s
def finishOperandFields (s : OperandFields) : JsonReader.Parser (Draft.Operand) := do
  let discriminator ← required s.kind "kind"
  let allowed : List String := match discriminator with
    | "Copy" => ["kind", "place"]
    | "Move" => ["kind", "place"]
    | "Constant" => ["kind", "constant"]
    | "RuntimeChecks" => ["kind", "check"]
    | _ => ["kind"]
  rejectIncompatible allowed [("kind", s.kind.isSome), ("place", s.place.isSome), ("constant", s.constant.isSome), ("check", s.check.isSome)]
  match (← required s.kind "kind") with
  | "Copy" => pure (.Copy (← required s.place "place"))
  | "Move" => pure (.Move (← required s.place "place"))
  | "Constant" => pure (.Constant (← required s.constant "constant"))
  | "RuntimeChecks" => pure (.RuntimeChecks (← required s.check "check"))
  | _ => reject "unknown operand"
def operand : JsonReader.Parser (Draft.Operand) := do
  finishOperandFields (← object {} operandField)
structure WithRetagFields where
  kind : Option (String) := none
  performs_retag : Option (Bool) := none

def withRetagField (s : WithRetagFields) (key : String) : JsonReader.Parser (WithRetagFields) := do
  match key with
  | "kind" => return {s with kind := some (← string)}
  | "performs_retag" => return {s with performs_retag := some (← boolean)}
  | _ => skipValue; pure s
def finishWithRetagFields (s : WithRetagFields) : JsonReader.Parser (MIR.WithRetag) := do
  let k ← required s.kind "kind"
  unless (← required s.performs_retag "performs_retag") == (k == "yes") do reject "WithRetag boolean disagrees with tag"
  match k with
  | "yes" => pure .Yes
  | "no" => pure .No
  | _ => reject "unknown retag mode"
def withRetag : JsonReader.Parser (MIR.WithRetag) := do
  finishWithRetagFields (← object {} withRetagField)
structure TlsInitializerFields where
  allocation : Option (AllocationMemory) := none

def tlsInitializerField (s : TlsInitializerFields) (key : String) : JsonReader.Parser (TlsInitializerFields) := do
  match key with
  | "allocation" => return {s with allocation := some (← DecoderValues.parseAllocationMemory "$thread_local.initializer.allocation")}
  | _ => skipValue; pure s
def finishTlsInitializerFields (s : TlsInitializerFields) : JsonReader.Parser (Option AllocationMemory) := do
  pure s.allocation
def tlsInitializer : JsonReader.Parser (Option AllocationMemory) := do
  finishTlsInitializerFields (← object {} tlsInitializerField)
private def enumTag : JsonReader.Parser (String) := do
  if (← peek!) == '"' then string
  else
    let value ← object (none : Option String) fun state key => do
      if key == "kind" then return some (← string)
      else skipValue; pure state
    required value "kind"

private def rawPointer : JsonReader.Parser (MIR.RawPtrKind) := do
  match ← enumTag with
  | "mutable" => pure .Mut
  | "constant" => pure .Const
  | "metadata_only" => pure .FakeForPtrMetadata
  | _ => reject "unknown raw pointer kind"

private def binOpTag (value : String) : Result MIR.BinOp := do
  match value with
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
    | _ => throw "unknown binary operator"


private def unOpTag (value : String) : Result MIR.UnOp := do
  match value with
    | "not" => pure .Not
    | "negate" => pure .Neg
    | "pointer_metadata" => pure .PtrMetadata
    | _ => throw "unknown unary operator"


structure RvalueFields where
  kind : Option (String) := none
  operand : Option (Draft.Operand) := none
  left : Option (Draft.Operand) := none
  right : Option (Draft.Operand) := none
  operands : Option (Array Draft.Operand) := none
  retag : Option (MIR.WithRetag) := none
  operator : Option (String) := none
  place : Option (Draft.Place) := none
  type : Option (Nat) := none
  target_type : Option (Nat) := none
  count : Option (Nat) := none
  region : Option (MIR.Region) := none
  borrow_kind : Option (MIR.BorrowKind) := none
  pointer_kind : Option (MIR.RawPtrKind) := none
  cast_kind : Option (MIR.CastKind) := none
  aggregate_kind : Option (MIR.AggregateKind) := none
  mutability : Option (MIR.Mutability) := none
  def_id : Option (Nat) := none
  global_info : Option (StaticGlobalInfo) := none
  initializer : Option (Option AllocationMemory) := none
  vtable_allocation : Option (Option DynamicUpcastEvidence) := none

def rvalueField (s : RvalueFields) (key : String) : JsonReader.Parser (RvalueFields) := do
  match key with
  | "kind" => return {s with kind := some (← string)}
  | "operand" => return {s with operand := some (← operand)}
  | "left" => return {s with left := some (← operand)}
  | "right" => return {s with right := some (← operand)}
  | "operands" => return {s with operands := some (← array operand)}
  | "retag" => return {s with retag := some (← withRetag)}
  | "operator" => return {s with operator := some (← enumTag)}
  | "place" => return {s with place := some (← place)}
  | "type" => return {s with type := some (← natural)}
  | "target_type" => return {s with target_type := some (← natural)}
  | "count" => return {s with count := some (← natural)}
  | "region" => return {s with region := some (← GenericArgsCodec.region)}
  | "borrow_kind" => return {s with borrow_kind := some (← borrow)}
  | "pointer_kind" => return {s with pointer_kind := some (← rawPointer)}
  | "cast_kind" => return {s with cast_kind := some (← castKind)}
  | "aggregate_kind" => return {s with aggregate_kind := some (← aggregate)}
  | "mutability" => return {s with mutability := some (← mutability)}
  | "def_id" => return {s with def_id := some (← natural)}
  | "global_info" => return {s with global_info := some (← DecoderValues.decodeStaticGlobalInfo)}
  | "initializer" => return {s with initializer := some (← tlsInitializer)}
  | "vtable_allocation" => return {s with vtable_allocation := some (← upcast)}
  | _ => skipValue; pure s
def finishRvalueFields (s : RvalueFields) : JsonReader.Parser (Draft.Rvalue) := do
  let discriminator ← required s.kind "kind"
  let allowed : List String := match discriminator with
    | "Use" => ["kind", "operand", "retag"]
    | "BinaryOp" => ["kind", "operator", "left", "right"]
    | "UnaryOp" => ["kind", "operator", "operand"]
    | "Discriminant" => ["kind", "place"]
    | "CopyForDeref" => ["kind", "place"]
    | "WrapUnsafeBinder" => ["kind", "operand", "type"]
    | "Repeat" => ["kind", "operand", "count"]
    | "Ref" => ["kind", "region", "borrow_kind", "place"]
    | "ThreadLocalRef" => ["kind", "def_id", "global_info", "initializer"]
    | "RawPtr" => ["kind", "pointer_kind", "place"]
    | "Cast" => ["kind", "cast_kind", "operand", "target_type", "vtable_allocation"]
    | "Aggregate" => ["kind", "aggregate_kind", "operands"]
    | "Reborrow" => ["kind", "type", "mutability", "place"]
    | _ => ["kind"]
  rejectIncompatible allowed [("kind", s.kind.isSome), ("operand", s.operand.isSome), ("left", s.left.isSome), ("right", s.right.isSome), ("operands", s.operands.isSome), ("retag", s.retag.isSome), ("operator", s.operator.isSome), ("place", s.place.isSome), ("type", s.type.isSome), ("target_type", s.target_type.isSome), ("count", s.count.isSome), ("region", s.region.isSome), ("borrow_kind", s.borrow_kind.isSome), ("pointer_kind", s.pointer_kind.isSome), ("cast_kind", s.cast_kind.isSome), ("aggregate_kind", s.aggregate_kind.isSome), ("mutability", s.mutability.isSome), ("def_id", s.def_id.isSome), ("global_info", s.global_info.isSome), ("initializer", s.initializer.isSome), ("vtable_allocation", s.vtable_allocation.isSome)]
  match (← required s.kind "kind") with
  | "Use" => pure (.Use (← required s.operand "operand") (← required s.retag "retag"))
  | "BinaryOp" => pure (.BinaryOp (← liftExcept (binOpTag (← required s.operator "operator"))) (← required s.left "left") (← required s.right "right"))
  | "UnaryOp" => pure (.UnaryOp (← liftExcept (unOpTag (← required s.operator "operator"))) (← required s.operand "operand"))
  | "Discriminant" => pure (.Discriminant (← required s.place "place"))
  | "CopyForDeref" => pure (.CopyForDeref (← required s.place "place"))
  | "WrapUnsafeBinder" => pure (.WrapUnsafeBinder (← required s.operand "operand") (← required s.type "type"))
  | "Repeat" => pure (.Repeat (← required s.operand "operand") (← required s.count "count"))
  | "Ref" => pure (.Ref (← required s.region "region") (← required s.borrow_kind "borrow_kind") (← required s.place "place"))
  | "ThreadLocalRef" =>
    let info ← required s.global_info "global_info"
    unless info.isStatic && info.threadLocal do reject "TLS declaration compiler query evidence is unresolved or inconsistent"
    let initializer ← required s.initializer "initializer"
    if !info.foreignItem && initializer.isNone then reject "missing TLS initializer allocation"
    pure (.ThreadLocalRef ⟨(← required s.def_id "def_id"), info, if info.foreignItem then none else initializer⟩)
  | "RawPtr" => pure (.RawPtr (← required s.pointer_kind "pointer_kind") (← required s.place "place"))
  | "Cast" =>
    let kind ← required s.cast_kind "cast_kind"
    let desc := s.vtable_allocation.join
    if desc.isSome then
      match kind with
      | .PointerCoercion .Unsize _ => pure ()
      | _ => reject "dynamic vtable descriptor requires an unsizing cast"
    pure (.Cast kind (← required s.operand "operand") (← required s.target_type "target_type") desc)
  | "Aggregate" => pure (.Aggregate (← required s.aggregate_kind "aggregate_kind") (← required s.operands "operands"))
  | "Reborrow" => pure (.Reborrow (← required s.type "type") (← required s.mutability "mutability") (← required s.place "place"))
  | _ => reject "unknown rvalue"
def rvalue : JsonReader.Parser (Draft.Rvalue) := do
  finishRvalueFields (← object {} rvalueField)
structure StatementKindFields where
  variant : Option (String) := none
  place : Option (Draft.Place) := none
  rvalue : Option (Draft.Rvalue) := none
  «local» : Option (Nat) := none
  variant_index : Option (Nat) := none
  cause : Option (MIR.FakeReadCause) := none
  user_type_projection : Option (MIR.UserTypeProjection) := none
  variance : Option (MIR.Variance) := none
  coverage : Option (MIR.CoverageKind) := none
  intrinsic : Option (String) := none
  value : Option (Draft.Operand) := none
  src : Option (Draft.Operand) := none
  dst : Option (Draft.Operand) := none
  count : Option (Draft.Operand) := none
  reason : Option (String) := none

def statementKindField (s : StatementKindFields) (key : String) : JsonReader.Parser (StatementKindFields) := do
  match key with
  | "variant" => return {s with variant := some (← string)}
  | "place" => return {s with place := some (← place)}
  | "rvalue" => return {s with rvalue := some (← rvalue)}
  | "local" => return {s with «local» := some (← natural)}
  | "variant_index" => return {s with variant_index := some (← natural)}
  | "cause" => return {s with cause := some (← fakeRead)}
  | "user_type_projection" => return {s with user_type_projection := some (← userProjection)}
  | "variance" => return {s with variance := some (← variance)}
  | "coverage" => return {s with coverage := some (← coverage)}
  | "intrinsic" => return {s with intrinsic := some (← string)}
  | "value" => return {s with value := some (← operand)}
  | "src" => return {s with src := some (← operand)}
  | "dst" => return {s with dst := some (← operand)}
  | "count" => return {s with count := some (← operand)}
  | "reason" => return {s with reason := some (← enumTag)}
  | _ => skipValue; pure s
def finishStatementKindFields (s : StatementKindFields) : JsonReader.Parser (Draft.StatementKind) := do
  let discriminator ← required s.variant "variant"
  let allowed : List String := match discriminator with
    | "Assign" => ["variant", "place", "rvalue"]
    | "StorageLive" => ["variant", "local"]
    | "StorageDead" => ["variant", "local"]
    | "PlaceMention" => ["variant", "place"]
    | "SetDiscriminant" => ["variant", "place", "variant_index"]
    | "ConstEvalCounter" => ["variant"]
    | "Nop" => ["variant"]
    | "FakeRead" => ["variant", "cause", "place"]
    | "AscribeUserType" => ["variant", "place", "user_type_projection", "variance"]
    | "Coverage" => ["variant", "coverage"]
    | "Intrinsic" => ["variant", "intrinsic", "value", "src", "dst", "count"]
    | "BackwardIncompatibleDropHint" => ["variant", "reason", "place"]
    | _ => ["variant"]
  rejectIncompatible allowed [("variant", s.variant.isSome), ("place", s.place.isSome), ("rvalue", s.rvalue.isSome), ("local", s.«local».isSome), ("variant_index", s.variant_index.isSome), ("cause", s.cause.isSome), ("user_type_projection", s.user_type_projection.isSome), ("variance", s.variance.isSome), ("coverage", s.coverage.isSome), ("intrinsic", s.intrinsic.isSome), ("value", s.value.isSome), ("src", s.src.isSome), ("dst", s.dst.isSome), ("count", s.count.isSome), ("reason", s.reason.isSome)]
  match (← required s.variant "variant") with
  | "Assign" => pure (.Assign (← required s.place "place") (← required s.rvalue "rvalue"))
  | "StorageLive" => pure (.StorageLive (← required s.«local» "local"))
  | "StorageDead" => pure (.StorageDead (← required s.«local» "local"))
  | "PlaceMention" => pure (.PlaceMention (← required s.place "place"))
  | "SetDiscriminant" => pure (.SetDiscriminant (← required s.place "place") (← required s.variant_index "variant_index"))
  | "ConstEvalCounter" => pure .ConstEvalCounter
  | "Nop" => pure .Nop
  | "FakeRead" => pure (.FakeRead (← required s.cause "cause") (← required s.place "place"))
  | "AscribeUserType" => pure (.AscribeUserType (← required s.place "place") (← required s.user_type_projection "user_type_projection") (← required s.variance "variance"))
  | "Coverage" => pure (.Coverage (← required s.coverage "coverage"))
  | "Intrinsic" =>
    match (← required s.intrinsic "intrinsic") with
    | "Assume" => pure (.Intrinsic (.Assume (← required s.value "value")))
    | "CopyNonOverlapping" => pure (.Intrinsic (.CopyNonOverlapping ⟨(← required s.src "src"), (← required s.dst "dst"), (← required s.count "count")⟩))
    | _ => reject "unknown nondiverging intrinsic"
  | "BackwardIncompatibleDropHint" =>
    unless (← required s.reason "reason") == "edition_2024" do reject "unknown backward drop reason"
    pure (.BackwardIncompatibleDropHint (← required s.place "place") .Edition2024)
  | _ => reject "unknown statement"
def statementKind : JsonReader.Parser (Draft.StatementKind) := do
  finishStatementKindFields (← object {} statementKindField)
structure StatementFields where
  source_info : Option (MIR.SourceInfo) := none
  kind : Option (Draft.StatementKind) := none

def statementField (s : StatementFields) (key : String) : JsonReader.Parser (StatementFields) := do
  match key with
  | "source_info" => return {s with source_info := some (← source)}
  | "kind" => return {s with kind := some (← statementKind)}
  | _ => skipValue; pure s
def finishStatementFields (s : StatementFields) : JsonReader.Parser (Draft.Statement) := do
  return ⟨(← required s.source_info "source_info"), (← required s.kind "kind")⟩
def statement : JsonReader.Parser (Draft.Statement) := do
  finishStatementFields (← object {} statementField)
structure AssertKindFields where
  kind : Option (String) := none
  operator : Option (MIR.BinOp) := none
  left : Option (Draft.Operand) := none
  right : Option (Draft.Operand) := none
  length : Option (Draft.Operand) := none
  index : Option (Draft.Operand) := none
  operand : Option (Draft.Operand) := none
  required : Option (Draft.Operand) := none
  found : Option (Draft.Operand) := none
  coroutine_kind : Option (MIR.CoroutineKind) := none

def assertKindField (s : AssertKindFields) (key : String) : JsonReader.Parser (AssertKindFields) := do
  match key with
  | "kind" => return {s with kind := some (← string)}
  | "operator" => return {s with operator := some (← binOp)}
  | "left" => return {s with left := some (← operand)}
  | "right" => return {s with right := some (← operand)}
  | "length" => return {s with length := some (← operand)}
  | "index" => return {s with index := some (← operand)}
  | "operand" => return {s with operand := some (← operand)}
  | "required" => return {s with required := some (← operand)}
  | "found" => return {s with found := some (← operand)}
  | "coroutine_kind" => return {s with coroutine_kind := some (← coroutine)}
  | _ => skipValue; pure s
def finishAssertKindFields (s : AssertKindFields) : JsonReader.Parser (Draft.AssertKind) := do
  let discriminator ← required s.kind "kind"
  let allowed : List String := match discriminator with
    | "Overflow" => ["kind", "operator", "left", "right"]
    | "BoundsCheck" => ["kind", "length", "index"]
    | "OverflowNeg" => ["kind", "operand"]
    | "DivisionByZero" => ["kind", "operand"]
    | "RemainderByZero" => ["kind", "operand"]
    | "NullPointerDereference" => ["kind"]
    | "NullReferenceConstructed" => ["kind"]
    | "ResumedAfterReturn" => ["kind", "coroutine_kind"]
    | "ResumedAfterPanic" => ["kind", "coroutine_kind"]
    | "ResumedAfterDrop" => ["kind", "coroutine_kind"]
    | "MisalignedPointerDereference" => ["kind", "required", "found"]
    | "InvalidEnumConstruction" => ["kind", "operand"]
    | _ => ["kind"]
  rejectIncompatible allowed [("kind", s.kind.isSome), ("operator", s.operator.isSome), ("left", s.left.isSome), ("right", s.right.isSome), ("length", s.length.isSome), ("index", s.index.isSome), ("operand", s.operand.isSome), ("required", s.required.isSome), ("found", s.found.isSome), ("coroutine_kind", s.coroutine_kind.isSome)]
  match (← required s.kind "kind") with
  | "Overflow" => pure (.Overflow (← required s.operator "operator") (← required s.left "left") (← required s.right "right"))
  | "BoundsCheck" => pure (.BoundsCheck (← required s.length "length") (← required s.index "index"))
  | "OverflowNeg" => pure (.OverflowNeg (← required s.operand "operand"))
  | "DivisionByZero" => pure (.DivisionByZero (← required s.operand "operand"))
  | "RemainderByZero" => pure (.RemainderByZero (← required s.operand "operand"))
  | "NullPointerDereference" => pure .NullPointerDereference
  | "NullReferenceConstructed" => pure .NullReferenceConstructed
  | "ResumedAfterReturn" => pure (.ResumedAfterReturn (← required s.coroutine_kind "coroutine_kind"))
  | "ResumedAfterPanic" => pure (.ResumedAfterPanic (← required s.coroutine_kind "coroutine_kind"))
  | "ResumedAfterDrop" => pure (.ResumedAfterDrop (← required s.coroutine_kind "coroutine_kind"))
  | "MisalignedPointerDereference" => pure (.MisalignedPointerDereference (← required s.required "required") (← required s.found "found"))
  | "InvalidEnumConstruction" => pure (.InvalidEnumConstruction (← required s.operand "operand"))
  | _ => reject "unknown assertion kind"
def assertKind : JsonReader.Parser (Draft.AssertKind) := do
  finishAssertKindFields (← object {} assertKindField)
structure SpannedOperandFields where
  span : Option (Nat) := none
  operand : Option (Draft.Operand) := none

def spannedOperandField (s : SpannedOperandFields) (key : String) : JsonReader.Parser (SpannedOperandFields) := do
  match key with
  | "span" => return {s with span := some (← natural)}
  | "operand" => return {s with operand := some (← operand)}
  | _ => skipValue; pure s
def finishSpannedOperandFields (s : SpannedOperandFields) : JsonReader.Parser (Draft.SpannedOperand) := do
  return ⟨⟨(← required s.span "span")⟩, (← required s.operand "operand")⟩
def spannedOperand : JsonReader.Parser (Draft.SpannedOperand) := do
  finishSpannedOperandFields (← object {} spannedOperandField)
/-- The `value` member in inline assembly is an operand for `in`, but a
constant operand for `const` and `sym_fn`. Both are parsed forward into this
schema-specific union before the enclosing tag is inspected. -/
private structure AsmConstantFields where
  kind : Option String := none
  value : Option DraftConstValue := none
  type : Option Nat := none
  span : Option Nat := none
  user_type_annotation : Option (Option Nat) := none
  constant : Option (DraftConstValue) := none

private def asmConstant : JsonReader.Parser ((Sum (DraftConstValue) DraftConstant)) := do
  let s ← object ({} : AsmConstantFields) fun s key => do
    match key with
    | "kind" => return {s with kind := some (← string)}
    | "value" => return {s with value := some (← parseConstValue)}
    | "type" => return {s with type := some (← natural)}
    | "span" => return {s with span := some (← natural)}
    | "user_type_annotation" => return {s with user_type_annotation := some (← nullable annotation)}
    | "constant" => return {s with constant := some (← parseEvaluated)}
    | _ => skipValue; pure s
  match s.kind with
  | some "evaluated_const" =>
    return .inl (← required s.value "value")
  | none =>
    let c ← required s.constant "constant"
    return .inr ⟨(← required s.type "type"), ⟨(← required s.span "span")⟩,
      (← required s.user_type_annotation "user_type_annotation"), c⟩
  | _ => reject "unknown assembly constant record"

structure AsmValueFields where
  kind : Option String := none
  place : Option Draft.Place := none
  constant : Option (Sum (DraftConstValue) DraftConstant) := none
  check : Option MIR.RuntimeChecks := none
  type : Option Nat := none
  span : Option Nat := none
  user_type_annotation : Option (Option Nat) := none

def asmValueField (s : AsmValueFields) (key : String) : JsonReader.Parser (AsmValueFields) := do
  match key with
  | "kind" => return {s with kind := some (← string)}
  | "place" => return {s with place := some (← place)}
  | "constant" => return {s with constant := some (← asmConstant)}
  | "check" => return {s with check := some (← runtimeCheck)}
  | "type" => return {s with type := some (← natural)}
  | "span" => return {s with span := some (← natural)}
  | "user_type_annotation" => return {s with user_type_annotation := some (← nullable annotation)}
  | _ => skipValue; pure s
def finishAsmValueFields (s : AsmValueFields) : JsonReader.Parser (Draft.Operand) := do
  match s.kind with
  | some "Copy" => pure (.Copy (← required s.place "place"))
  | some "Move" => pure (.Move (← required s.place "place"))
  | some "RuntimeChecks" => pure (.RuntimeChecks (← required s.check "check"))
  | some "Constant" =>
    let .inr c ← required s.constant "constant" | reject "expected assembly constant operand"
    pure (.Constant c)
  | none =>
    let .inl c ← required s.constant "constant" | reject "expected assembly evaluated constant"
    pure (.Constant ⟨(← required s.type "type"), ⟨(← required s.span "span")⟩,
      (← required s.user_type_annotation "user_type_annotation"), c⟩)
  | _ => reject "unknown inline assembly input operand"
def asmValue : JsonReader.Parser (Draft.Operand) := do
  finishAsmValueFields (← object {} asmValueField)
structure AsmOperandFields where
  kind : Option (String) := none
  register : Option (MIR.InlineAsmRegOrRegClass) := none
  value : Option (Draft.Operand) := none
  late : Option (Bool) := none
  place : Option (Option Draft.Place) := none
  input : Option (Draft.Operand) := none
  output : Option (Option Draft.Place) := none
  def_id : Option (Nat) := none
  target_index : Option (Nat) := none

def asmOperandField (s : AsmOperandFields) (key : String) : JsonReader.Parser (AsmOperandFields) := do
  match key with
  | "kind" => return {s with kind := some (← string)}
  | "register" => return {s with register := some (← asmRegister)}
  | "value" => return {s with value := some (← asmValue)}
  | "late" => return {s with late := some (← boolean)}
  | "place" => return {s with place := some (← nullable place)}
  | "input" => return {s with input := some (← operand)}
  | "output" => return {s with output := some (← nullable place)}
  | "def_id" => return {s with def_id := some (← natural)}
  | "target_index" => return {s with target_index := some (← natural)}
  | _ => skipValue; pure s
def finishAsmOperandFields (s : AsmOperandFields) : JsonReader.Parser (Draft.InlineAsmOperand) := do
  let discriminator ← required s.kind "kind"
  let allowed : List String := match discriminator with
    | "in" => ["kind", "register", "value"]
    | "out" => ["kind", "register", "late", "place"]
    | "inout" => ["kind", "register", "late", "input", "output"]
    | "const" => ["kind", "value"]
    | "sym_fn" => ["kind", "value"]
    | "sym_static" => ["kind", "def_id"]
    | "label" => ["kind", "target_index"]
    | _ => ["kind"]
  rejectIncompatible allowed [("kind", s.kind.isSome), ("register", s.register.isSome), ("value", s.value.isSome), ("late", s.late.isSome), ("place", s.place.isSome), ("input", s.input.isSome), ("output", s.output.isSome), ("def_id", s.def_id.isSome), ("target_index", s.target_index.isSome)]
  match (← required s.kind "kind") with
  | "in" => pure (.In (← required s.register "register") (← required s.value "value"))
  | "out" => pure (.Out (← required s.register "register") (← required s.late "late") (← required s.place "place"))
  | "inout" => pure (.InOut (← required s.register "register") (← required s.late "late") (← required s.input "input") (← required s.output "output"))
  | "const" | "sym_fn" =>
    let .Constant c := (← required s.value "value") | reject "expected assembly constant"
    if (← required s.kind "kind") == "const" then pure (.Const c) else pure (.SymFn c)
  | "sym_static" => pure (.SymStatic (← required s.def_id "def_id"))
  | "label" => pure (.Label (← required s.target_index "target_index"))
  | _ => reject "unknown assembly operand"
def asmOperand : JsonReader.Parser (Draft.InlineAsmOperand) := do
  finishAsmOperandFields (← object {} asmOperandField)
structure AsmOptionsFields where
  pure : Option (Bool) := none
  nomem : Option (Bool) := none
  readonly : Option (Bool) := none
  preserves_flags : Option (Bool) := none
  noreturn : Option (Bool) := none
  nostack : Option (Bool) := none
  att_syntax : Option (Bool) := none
  raw : Option (Bool) := none
  may_unwind : Option (Bool) := none

def asmOptionsField (s : AsmOptionsFields) (key : String) : JsonReader.Parser (AsmOptionsFields) := do
  match key with
  | "pure" => return {s with pure := some (← boolean)}
  | "nomem" => return {s with nomem := some (← boolean)}
  | "readonly" => return {s with readonly := some (← boolean)}
  | "preserves_flags" => return {s with preserves_flags := some (← boolean)}
  | "noreturn" => return {s with noreturn := some (← boolean)}
  | "nostack" => return {s with nostack := some (← boolean)}
  | "att_syntax" => return {s with att_syntax := some (← boolean)}
  | "raw" => return {s with raw := some (← boolean)}
  | "may_unwind" => return {s with may_unwind := some (← boolean)}
  | _ => skipValue; pure s
def finishAsmOptionsFields (s : AsmOptionsFields) : JsonReader.Parser (MIR.InlineAsmOptions) := do
  return ⟨(← required s.pure "pure"), (← required s.nomem "nomem"), (← required s.readonly "readonly"), (← required s.preserves_flags "preserves_flags"), (← required s.noreturn "noreturn"), (← required s.nostack "nostack"), (← required s.att_syntax "att_syntax"), (← required s.raw "raw"), (← required s.may_unwind "may_unwind")⟩
def asmOptions : JsonReader.Parser (MIR.InlineAsmOptions) := do
  finishAsmOptionsFields (← object {} asmOptionsField)
structure SwitchTargetFields where
  value : Option (Nat) := none
  target : Option (Nat) := none

def switchTargetField (s : SwitchTargetFields) (key : String) : JsonReader.Parser (SwitchTargetFields) := do
  match key with
  | "value" => return {s with value := some (← number)}
  | "target" => return {s with target := some (← natural)}
  | _ => skipValue; pure s
def finishSwitchTargetFields (s : SwitchTargetFields) : JsonReader.Parser (MIR.SwitchTarget) := do
  return .Case (← required s.value "value") (← required s.target "target")
def switchTarget : JsonReader.Parser (MIR.SwitchTarget) := do
  finishSwitchTargetFields (← object {} switchTargetField)
inductive DraftTarget where
  | case (value : MIR.SwitchTarget)
  | block (value : Nat)
private def targetItem : JsonReader.Parser (DraftTarget) := do
  if (← peek!) == '{' then .case <$> switchTarget
  else .block <$> natural

structure TerminatorKindFields where
  variant : Option (String) := none
  condition : Option (Draft.Operand) := none
  expected : Option (Bool) := none
  message : Option (Draft.AssertKind) := none
  target : Option (Option Nat) := none
  unwind : Option (MIR.UnwindAction) := none
  real_target : Option (Nat) := none
  imaginary_target : Option (Nat) := none
  loop_hints : Option (Array MIR.LoopHintAttr) := none
  discriminant : Option (Draft.Operand) := none
  targets : Option (Array DraftTarget) := none
  otherwise : Option (Nat) := none
  reason : Option (MIR.UnwindTerminateReason) := none
  place : Option (Draft.Place) := none
  replace : Option (Bool) := none
  async_drop : Option (Option Nat) := none
  function : Option (Draft.Operand) := none
  args : Option (Array Draft.SpannedOperand) := none
  destination : Option (Draft.Place) := none
  call_source : Option (MIR.CallSource) := none
  function_span : Option (Nat) := none
  value : Option (Draft.Operand) := none
  resume : Option (Nat) := none
  resume_arg : Option (Draft.Place) := none
  drop : Option (Option Nat) := none
  resolution : Option (CallResolutionEvidence) := none
  asm_macro : Option (String) := none
  options : Option (MIR.InlineAsmOptions) := none
  template : Option (Array MIR.InlineAsmTemplatePiece) := none
  operands : Option (Array Draft.InlineAsmOperand) := none
  line_spans : Option (Array Nat) := none

def terminatorKindField (s : TerminatorKindFields) (key : String) : JsonReader.Parser (TerminatorKindFields) := do
  match key with
  | "variant" => return {s with variant := some (← string)}
  | "condition" => return {s with condition := some (← operand)}
  | "expected" => return {s with expected := some (← boolean)}
  | "message" => return {s with message := some (← assertKind)}
  | "target" => return {s with target := some (← nullable natural)}
  | "unwind" => return {s with unwind := some (← unwind)}
  | "real_target" => return {s with real_target := some (← natural)}
  | "imaginary_target" => return {s with imaginary_target := some (← natural)}
  | "loop_hints" => return {s with loop_hints := some (← array loopHint)}
  | "discriminant" => return {s with discriminant := some (← operand)}
  | "targets" => return {s with targets := some (← array targetItem)}
  | "otherwise" => return {s with otherwise := some (← natural)}
  | "reason" => return {s with reason := some (← unwindReason)}
  | "place" => return {s with place := some (← place)}
  | "replace" => return {s with replace := some (← boolean)}
  | "async_drop" => return {s with async_drop := some (← nullable natural)}
  | "function" => return {s with function := some (← operand)}
  | "args" => return {s with args := some (← array spannedOperand)}
  | "destination" => return {s with destination := some (← place)}
  | "call_source" => return {s with call_source := some (← callSource)}
  | "function_span" => return {s with function_span := some (← natural)}
  | "value" => return {s with value := some (← operand)}
  | "resume" => return {s with resume := some (← natural)}
  | "resume_arg" => return {s with resume_arg := some (← place)}
  | "drop" => return {s with drop := some (← nullable natural)}
  | "resolution" => return {s with resolution := some (← callEvidence)}
  | "asm_macro" => return {s with asm_macro := some (← string)}
  | "options" => return {s with options := some (← asmOptions)}
  | "template" => return {s with template := some (← array asmPiece)}
  | "operands" => return {s with operands := some (← array asmOperand)}
  | "line_spans" => return {s with line_spans := some (← array natural)}
  | _ => skipValue; pure s
def finishTerminatorKindFields (s : TerminatorKindFields) : JsonReader.Parser (Draft.TerminatorKind × Option CallResolutionEvidence) := do
  let discriminator ← required s.variant "variant"
  let allowed : List String := match discriminator with
    | "Return" => ["variant"]
    | "Unreachable" => ["variant"]
    | "UnwindResume" => ["variant"]
    | "CoroutineDrop" => ["variant"]
    | "Assert" => ["variant", "condition", "expected", "message", "target", "unwind"]
    | "FalseEdge" => ["variant", "real_target", "imaginary_target"]
    | "Goto" => ["variant", "target", "loop_hints"]
    | "SwitchInt" => ["variant", "discriminant", "targets", "otherwise"]
    | "UnwindTerminate" => ["variant", "reason"]
    | "Drop" => ["variant", "place", "target", "unwind", "replace", "async_drop"]
    | "Call" => ["variant", "function", "args", "destination", "target", "unwind", "call_source", "function_span", "resolution"]
    | "TailCall" => ["variant", "function", "args", "function_span", "resolution"]
    | "Yield" => ["variant", "value", "resume", "resume_arg", "drop"]
    | "FalseUnwind" => ["variant", "real_target", "unwind"]
    | "InlineAsm" => ["variant", "asm_macro", "options", "template", "operands", "line_spans", "targets", "unwind"]
    | _ => ["variant"]
  rejectIncompatible allowed [("variant", s.variant.isSome), ("condition", s.condition.isSome), ("expected", s.expected.isSome), ("message", s.message.isSome), ("target", s.target.isSome), ("unwind", s.unwind.isSome), ("real_target", s.real_target.isSome), ("imaginary_target", s.imaginary_target.isSome), ("loop_hints", s.loop_hints.isSome), ("discriminant", s.discriminant.isSome), ("targets", s.targets.isSome), ("otherwise", s.otherwise.isSome), ("reason", s.reason.isSome), ("place", s.place.isSome), ("replace", s.replace.isSome), ("async_drop", s.async_drop.isSome), ("function", s.function.isSome), ("args", s.args.isSome), ("destination", s.destination.isSome), ("call_source", s.call_source.isSome), ("function_span", s.function_span.isSome), ("value", s.value.isSome), ("resume", s.resume.isSome), ("resume_arg", s.resume_arg.isSome), ("drop", s.drop.isSome), ("resolution", s.resolution.isSome), ("asm_macro", s.asm_macro.isSome), ("options", s.options.isSome), ("template", s.template.isSome), ("operands", s.operands.isSome), ("line_spans", s.line_spans.isSome)]
  let kind ← required s.variant "variant"
  let value ← match kind with
    | "Return" => pure Draft.TerminatorKind.Return
    | "Unreachable" => pure .Unreachable
    | "UnwindResume" => pure .UnwindResume
    | "CoroutineDrop" => pure .CoroutineDrop
    | "Assert" => pure (.Assert (← required s.condition "condition") (← required s.expected "expected") (← required s.message "message") (← required (← required s.target "target") "non-null target") (← required s.unwind "unwind"))
    | "FalseEdge" => pure (.FalseEdge (← required s.real_target "real_target") (← required s.imaginary_target "imaginary_target"))
    | "Goto" => pure (.Goto (← required (← required s.target "target") "non-null target") (← required s.loop_hints "loop_hints"))
    | "SwitchInt" =>
      let cases ← ((← required s.targets "targets")).mapM fun target => match target with
        | .case c => pure c
        | .block _ => reject "expected switch case"
      pure (.SwitchInt (← required s.discriminant "discriminant") ⟨cases, (← required s.otherwise "otherwise")⟩)
    | "UnwindTerminate" => pure (.UnwindTerminate (← required s.reason "reason"))
    | "Drop" => pure (.Drop (← required s.place "place") (← required (← required s.target "target") "non-null target") (← required s.unwind "unwind") (← required s.replace "replace") (← required s.async_drop "async_drop"))
    | "Call" => pure (.Call (← required s.function "function") (← required s.args "args") (← required s.destination "destination") (← required s.target "target") (← required s.unwind "unwind") (← required s.call_source "call_source") ⟨(← required s.function_span "function_span")⟩)
    | "TailCall" => pure (.TailCall (← required s.function "function") (← required s.args "args") ⟨(← required s.function_span "function_span")⟩)
    | "Yield" => pure (.Yield (← required s.value "value") (← required s.resume "resume") (← required s.resume_arg "resume_arg") (← required s.drop "drop"))
    | "FalseUnwind" => pure (.FalseUnwind (← required s.real_target "real_target") (← required s.unwind "unwind"))
    | "InlineAsm" =>
      let macroKind ← match (← required s.asm_macro "asm_macro") with
        | "asm" => pure MIR.InlineAsmMacro.Asm
        | "naked_asm" => pure .NakedAsm
        | _ => reject "unknown assembly macro"
      let targets ← ((← required s.targets "targets")).mapM fun target => match target with
        | .block n => pure n
        | .case _ => reject "expected assembly block target"
      let operands ← required s.operands "operands"
      let template ← required s.template "template"
      for op in operands do
        match op with
        | .Label index => unless index < targets.size do reject "assembly label index exceeds target list"
        | _ => pure ()
      for piece in template do
        match piece with
        | .Placeholder index _ _ => unless index < operands.size do reject "assembly placeholder exceeds operand list"
        | _ => pure ()
      pure (.InlineAsm ⟨macroKind, template, operands, (← required s.options "options"), ((← required s.line_spans "line_spans")).map MIR.SpanRef.mk, targets, (← required s.unwind "unwind")⟩)
    | _ => reject "unknown terminator"
  let evidence ← if kind == "Call" || kind == "TailCall" then some <$> required s.resolution "resolution" else pure none
  return (value, evidence)
def terminatorKind : JsonReader.Parser (Draft.TerminatorKind × Option CallResolutionEvidence) := do
  finishTerminatorKindFields (← object {} terminatorKindField)
structure TerminatorFields where
  source_info : Option (MIR.SourceInfo) := none
  kind : Option (Draft.TerminatorKind × Option CallResolutionEvidence) := none

def terminatorField (s : TerminatorFields) (key : String) : JsonReader.Parser (TerminatorFields) := do
  match key with
  | "source_info" => return {s with source_info := some (← source)}
  | "kind" => return {s with kind := some (← terminatorKind)}
  | _ => skipValue; pure s
def finishTerminatorFields (s : TerminatorFields) : JsonReader.Parser (Draft.Terminator) := do
  let pair ← required s.kind "kind"
  return ⟨(← required s.source_info "source_info"), pair.1, pair.2⟩
def terminator : JsonReader.Parser (Draft.Terminator) := do
  finishTerminatorFields (← object {} terminatorField)
structure BasicBlockFields where
  block : Option (Nat) := none
  statements : Option (Array Draft.Statement) := none
  terminator : Option (Draft.Terminator) := none
  is_cleanup : Option (Bool) := none

def basicBlockField (s : BasicBlockFields) (key : String) : JsonReader.Parser (BasicBlockFields) := do
  match key with
  | "block" => return {s with block := some (← natural)}
  | "statements" => return {s with statements := some (← array statement)}
  | "terminator" => return {s with terminator := some (← terminator)}
  | "is_cleanup" => return {s with is_cleanup := some (← boolean)}
  | _ => skipValue; pure s
def finishBasicBlockFields (s : BasicBlockFields) : JsonReader.Parser (Nat × Draft.BasicBlock) := do
  return ((← required s.block "block"), ⟨(← required s.statements "statements"), (← required s.terminator "terminator"), (← required s.is_cleanup "is_cleanup")⟩)
def basicBlock : JsonReader.Parser (Nat × Draft.BasicBlock) := do
  finishBasicBlockFields (← object {} basicBlockField)
structure LocalDeclFields where
  «local» : Option (Nat) := none
  type : Option (Nat) := none
  source_info : Option (Input.SourceInfo) := none

def localDeclField (s : LocalDeclFields) (key : String) : JsonReader.Parser (LocalDeclFields) := do
  match key with
  | "local" => return {s with «local» := some (← natural)}
  | "type" => return {s with type := some (← natural)}
  | "source_info" => return {s with source_info := some (← sourceInfo)}
  | _ => skipValue; pure s
def finishLocalDeclFields (s : LocalDeclFields) : JsonReader.Parser (LocalDecl) := do
  return ⟨(← required s.«local» "local"), (← required s.type "type"), (← required s.source_info "source_info")⟩
def localDecl : JsonReader.Parser (LocalDecl) := do
  finishLocalDeclFields (← object {} localDeclField)
structure PromotedBodyFields where
  promoted_index : Option (Option Nat) := none
  body : Option (Option Nat) := none

def promotedBodyField (s : PromotedBodyFields) (key : String) : JsonReader.Parser (PromotedBodyFields) := do
  match key with
  | "promoted_index" => return {s with promoted_index := some (← nullable natural)}
  | "body" => return {s with body := some (← nullable natural)}
  | _ => skipValue; pure s
def finishPromotedBodyFields (s : PromotedBodyFields) : JsonReader.Parser (PromotedBody) := do
  return ⟨s.promoted_index.join.getD 0, s.body.join⟩
def promotedBody : JsonReader.Parser (PromotedBody) := do
  finishPromotedBodyFields (← object {} promotedBodyField)
structure ParseBodyFields where
  phase : Option (MIR.MirPhase) := none
  arg_count : Option (Nat) := none
  spread_arg : Option (Option Nat) := none
  locals : Option (Array LocalDecl) := none
  basic_blocks : Option (Array (Nat × Draft.BasicBlock)) := none
  def_id : Option (Option Nat) := none
  source_def_id : Option (Option Nat) := none
  def_path : Option (Option String) := none
  span : Option (Nat) := none
  preamble_def_span : Option (Nat) := none
  injection_phase : Option (Option MIR.MirPhase) := none
  instance_id : Option Nat := none
  source_scopes : Option (Array SourceScope) := none
  backtrace_spans : Option (Array BacktraceSpan) := none
  required_consts : Option (Array DraftConstant) := none
  promoted_bodies : Option (Array PromotedBody) := none

def parseBodyField (s : ParseBodyFields) (key : String) : JsonReader.Parser (ParseBodyFields) := do
  match key with
  | "phase" => return {s with phase := some (← phase)}
  | "arg_count" => return {s with arg_count := some (← natural)}
  | "spread_arg" => return {s with spread_arg := some (← nullable natural)}
  | "locals" => return {s with locals := some (← array localDecl)}
  | "basic_blocks" => return {s with basic_blocks := some (← array basicBlock)}
  | "def_id" => return {s with def_id := some (← nullable natural)}
  | "source_def_id" => return {s with source_def_id := some (← nullable natural)}
  | "def_path" => return {s with def_path := some (← nullable string)}
  | "span" => return {s with span := some (← natural)}
  | "preamble_def_span" => return {s with preamble_def_span := some (← natural)}
  | "injection_phase" => return {s with injection_phase := some (← nullable phase)}
  | "instance_id" => return {s with instance_id := some (← natural)}
  | "source_scopes" => return {s with source_scopes := some (← array scope)}
  | "backtrace_spans" => return {s with backtrace_spans := some (← array backtrace)}
  | "required_consts" => return {s with required_consts := some (← array parseConstOperand)}
  | "promoted_bodies" => return {s with promoted_bodies := some (← array promotedBody)}
  | _ => skipValue; pure s
def finishParseBodyFields (s : ParseBodyFields) : JsonReader.Parser (DraftBody) := do
  let blocks ← required s.basic_blocks "basic_blocks"
  for (pair, index) in blocks.toList.zipIdx do
    unless pair.1 == index do reject "noncontiguous basic block IDs"
  return {
    phase := (← required s.phase "phase"), argumentCount := (← required s.arg_count "arg_count"), spreadArgument := s.spread_arg.join,
    locals := (← required s.locals "locals"), blocks := blocks.map Prod.snd,
    definitionId := s.def_id.join.orElse (fun _ => s.source_def_id.join), defPath := s.def_path.join,
    spanId := (← required s.span "span"), preambleDefSpanId := (← required s.preamble_def_span "preamble_def_span"),
    injectionPhase := s.injection_phase.join, instanceId := (← required s.instance_id "instance_id"),
    sourceScopes := (← required s.source_scopes "source_scopes"), backtraceSpans := (← required s.backtrace_spans "backtrace_spans"),
    requiredConsts := (← required s.required_consts "required_consts"),
    promotedBodies := s.promoted_bodies.getD #[] }
def parseBodyRaw : JsonReader.Parser (DraftBody) := do
  finishParseBodyFields (← object {} parseBodyField)

structure Context where
  typeCount : Nat
  allocationCount : Nat
  definitionCount : Nat
  typeConstantCount : Nat
  spanCount : Nat
  scalarSizes : Array (Option Nat)
  localCount : Nat := 0
  blockCount : Nat := 0
  scopeCount : Nat := 0

private abbrev ResolveM := StateT NodeFacts (ReaderT Context (Except String))
private def runResolve (ctx : Context) (action : ResolveM α) : Result α :=
  ((action.run {}).run ctx).map Prod.fst
private def runFacts (ctx : Context) (action : ResolveM α) : Result (α × NodeFacts) :=
  (action.run {}).run ctx
private def check (id count : Nat) (what : String) : Result Unit := do
  unless id < count do throw s!"unresolved {what} {id}"
private def checkType (ctx : Context) (id : Nat) : Result Unit := check id ctx.typeCount "type"
private def checkDef (ctx : Context) (id : Nat) : Result Unit := check id ctx.definitionCount "definition"
private def checkSpan (ctx : Context) (id : Nat) : Result Unit := check id ctx.spanCount "source span"
private def checkRegion (ctx : Context) (r : MIR.Region) : Result Unit := do
  let bound (b : MIR.BoundRegionKind) : Result Unit := do
    match b with
    | .Named id => checkDef ctx id
    | _ => pure ()
  match r with
  | .Bound _ _ b | .Placeholder _ _ b => bound b
  | .LateParameter id b =>
    checkDef ctx id
    match b with
    | .Named id => checkDef ctx id
    | _ => pure ()
  | _ => pure ()
private def checkArgs (ctx : Context) (args : Array MIR.GenericArg) : Result Unit := do
  for arg in args do
    match arg with
    | .Type id => checkType ctx id
    | .Const id => check id ctx.typeConstantCount "type constant"
    | .Lifetime r => checkRegion ctx r
private def checkAggregate (ctx : Context) (a : MIR.AggregateKind) : Result Unit := do
  match a with
  | .Array ty | .RawPtr ty _ => checkType ctx ty
  | .Tuple => pure ()
  | .Adt d _ args _ _ | .Closure d args | .Coroutine d args | .CoroutineClosure d args =>
    checkDef ctx d; checkArgs ctx args
private def checkSource (ctx : Context) (s : MIR.SourceInfo) : Result Unit := do
  checkSpan ctx s.span.id
  check s.scope ctx.scopeCount "source scope"

def resolveConstValue (ctx : Context) (ty : Nat) (value : DraftConstValue) : Result MIR.ConstValue := do
  checkType ctx ty
  match value with
  | .scalar bits =>
    let some size := (ctx.scalarSizes[ty]?).join | throw s!"missing scalar byte width for type {ty}"
    unless size > 0 && bits < 2 ^ (8 * size) do throw "scalar bits exceed byte width"
    pure (.Scalar (.Int bits size))
  | .ready value =>
    match value with
    | .Scalar (.Ptr (.Allocation id _ _ _)) | .Slice id _ | .Indirect id _ =>
      check id ctx.allocationCount "allocation"
    | _ => pure ()
    pure value

private def resolveConstant (c : DraftConstant) : ResolveM MIR.ConstOperand := do
  let ctx ← read
  checkType ctx c.typeId
  checkSpan ctx c.span.id
  let evaluated ← resolveConstValue ctx c.typeId c.evaluated
  let value : MIR.ConstOperand := ⟨c.span, c.userType, .Val evaluated c.typeId⟩
  match evaluated with
  | .Scalar (.Ptr (.Allocation id _ _ _)) | .Slice id _ | .Indirect id _ =>
    modify fun facts => {facts with constantAllocations := facts.constantAllocations.push id}
  | _ => pure ()
  pure value

def resolveConstOperand (ctx : Context) (c : DraftConstant) : Result MIR.ConstOperand :=
  runResolve ctx (resolveConstant c)

private def resolvePlace (p : Draft.Place) : ResolveM MIR.Place := do
  let ctx ← read
  check p.value.localId ctx.localCount "local"
  checkType ctx p.typeId
  for ty in p.projectionTypes do checkType ctx ty
  for projection in p.value.projection do
    match projection with
    | .Field _ ty | .OpaqueCast ty | .UnwrapUnsafeBinder ty => checkType ctx ty
    | .Index id => check id ctx.localCount "local"
    | _ => pure ()
  modify fun facts => {facts with places := facts.places.push ⟨p.value, p.typeId, p.projectionTypes⟩}
  pure p.value

private def resolveOperand (o : Draft.Operand) : ResolveM MIR.Operand := do
  match o with
  | .Copy p => return .Copy (← resolvePlace p)
  | .Move p => return .Move (← resolvePlace p)
  | .Constant c => return .Constant (← resolveConstant c)
  | .RuntimeChecks check => pure (.RuntimeChecks check)

private def operandType : Draft.Operand → Result Nat
  | .Copy p | .Move p => pure p.typeId
  | .Constant c => pure c.typeId
  | _ => .error "dynamic vtable upcast lacks operand type"

private def resolveRvalue (r : Draft.Rvalue) : ResolveM MIR.Rvalue := do
  let ctx ← read
  match r with
  | .Use o retag => return .Use (← resolveOperand o) retag
  | .Repeat o count =>
    check count ctx.typeConstantCount "type constant"
    return .Repeat (← resolveOperand o) count
  | .Ref region borrow p =>
    checkRegion ctx region
    return .Ref region borrow (← resolvePlace p)
  | .ThreadLocalRef entry =>
    checkDef ctx entry.definition
    modify fun facts => {facts with threadLocals := facts.threadLocals.push entry}
    pure (.ThreadLocalRef entry.definition)
  | .RawPtr kind p => return .RawPtr kind (← resolvePlace p)
  | .Cast kind o ty desc =>
    checkType ctx ty
    if let some desc := desc then
      let operandType ← operandType o
      let desc := {desc with operandType, castTarget := ty}
      for id in #[desc.operandType, desc.castTarget, desc.sourceType, desc.targetType,
          desc.sourcePointeeType, desc.targetPointeeType, desc.sourceTailType, desc.targetTailType,
          desc.querySource, desc.queryTarget] do checkType ctx id
      modify fun facts => {facts with dynamicUpcasts := facts.dynamicUpcasts.push desc}
    return .Cast kind (← resolveOperand o) ty
  | .BinaryOp op l r => return .BinaryOp op (← resolveOperand l) (← resolveOperand r)
  | .UnaryOp op o => return .UnaryOp op (← resolveOperand o)
  | .Discriminant p => return .Discriminant (← resolvePlace p)
  | .Aggregate kind os =>
    checkAggregate ctx kind
    return .Aggregate kind (← (os.mapM fun o => (resolveOperand o)))
  | .CopyForDeref p => return .CopyForDeref (← resolvePlace p)
  | .WrapUnsafeBinder o ty =>
    checkType ctx ty
    return .WrapUnsafeBinder (← resolveOperand o) ty
  | .Reborrow ty mutability p =>
    checkType ctx ty
    return .Reborrow ty mutability (← resolvePlace p)

private def resolveStatement (s : Draft.Statement) : ResolveM MIR.Statement := do
  let ctx ← read
  checkSource ctx s.sourceInfo
  let kind : MIR.StatementKind ← match s.kind with
    | .Assign p r => pure (MIR.StatementKind.Assign (← resolvePlace p) (← resolveRvalue r))
    | .FakeRead cause p =>
      match cause with
      | .ForMatchedPlace (some id) | .ForLet (some id) => checkDef ctx id
      | _ => pure ()
      pure (.FakeRead cause (← resolvePlace p))
    | .SetDiscriminant p index => pure (.SetDiscriminant (← resolvePlace p) index)
    | .StorageLive id => check id ctx.localCount "local"; pure (.StorageLive id)
    | .StorageDead id => check id ctx.localCount "local"; pure (.StorageDead id)
    | .PlaceMention p => pure (.PlaceMention (← resolvePlace p))
    | .AscribeUserType p projection variance => pure (.AscribeUserType (← resolvePlace p) projection variance)
    | .Coverage c =>
      match c with
      | .Point _ hir => checkDef ctx hir.owner
      | _ => pure ()
      pure (.Coverage c)
    | .Intrinsic (.Assume o) => pure (.Intrinsic (.Assume (← resolveOperand o)))
    | .Intrinsic (.CopyNonOverlapping c) => pure (.Intrinsic (.CopyNonOverlapping ⟨← (resolveOperand c.source), ← (resolveOperand c.destination), ← (resolveOperand c.count)⟩))
    | .ConstEvalCounter => pure .ConstEvalCounter
    | .Nop => pure .Nop
    | .BackwardIncompatibleDropHint p reason => pure (.BackwardIncompatibleDropHint (← resolvePlace p) reason)
  pure ⟨s.sourceInfo, kind⟩

private def resolveAssert (a : Draft.AssertKind) : ResolveM MIR.AssertKind := do
  match a with
  | .BoundsCheck l i => return .BoundsCheck (← resolveOperand l) (← resolveOperand i)
  | .Overflow op l r => return .Overflow op (← resolveOperand l) (← resolveOperand r)
  | .OverflowNeg o => return .OverflowNeg (← resolveOperand o)
  | .DivisionByZero o => return .DivisionByZero (← resolveOperand o)
  | .RemainderByZero o => return .RemainderByZero (← resolveOperand o)
  | .ResumedAfterReturn c => pure (.ResumedAfterReturn c)
  | .ResumedAfterPanic c => pure (.ResumedAfterPanic c)
  | .ResumedAfterDrop c => pure (.ResumedAfterDrop c)
  | .MisalignedPointerDereference r f => return .MisalignedPointerDereference (← resolveOperand r) (← resolveOperand f)
  | .NullPointerDereference => pure .NullPointerDereference
  | .NullReferenceConstructed => pure .NullReferenceConstructed
  | .InvalidEnumConstruction o => return .InvalidEnumConstruction (← resolveOperand o)
private def resolveSpanned (o : Draft.SpannedOperand) : ResolveM MIR.SpannedOperand := do
  checkSpan (← read) o.span.id
  return ⟨o.span, ← (resolveOperand o.operand)⟩
private def resolveAsmOperand (o : Draft.InlineAsmOperand) : ResolveM MIR.InlineAsmOperand := do
  match o with
  | .In reg o => return .In reg (← resolveOperand o)
  | .Out reg late p => return .Out reg late (← p.mapM resolvePlace)
  | .InOut reg late o p => return .InOut reg late (← resolveOperand o) (← p.mapM resolvePlace)
  | .Const c => return .Const (← resolveConstant c)
  | .SymFn c => return .SymFn (← resolveConstant c)
  | .SymStatic id => checkDef (← read) id; pure (.SymStatic id)
  | .Label index => pure (.Label index)
private def resolveAsm (a : Draft.InlineAsmTerminator) : ResolveM MIR.InlineAsmTerminator := do
  let ctx ← read
  for s in a.lineSpans do checkSpan ctx s.id
  for p in a.template do
    match p with
    | .Placeholder _ _ s => checkSpan ctx s.id
    | _ => pure ()
  let operands ← (a.operands.mapM fun o => (resolveAsmOperand o))
  return ⟨a.asmMacro, a.template, operands, a.options, a.lineSpans, a.targets, a.unwind⟩

private def resolveTerminator (t : Draft.Terminator) : ResolveM MIR.Terminator := do
  let ctx ← read
  checkSource ctx t.sourceInfo
  if let some e := t.evidence then
    for ty in e.functionType do checkType ctx ty
  let kind : MIR.TerminatorKind ← match t.kind with
    | .Goto b hs => pure (MIR.TerminatorKind.Goto b hs)
    | .SwitchInt o ts => pure (.SwitchInt (← resolveOperand o) ts)
    | .UnwindResume => pure .UnwindResume
    | .UnwindTerminate r => pure (.UnwindTerminate r)
    | .Return => pure .Return
    | .Unreachable => pure .Unreachable
    | .Drop p b u r a => pure (.Drop (← resolvePlace p) b u r a)
    | .Call f args p b u s span =>
      checkSpan ctx span.id
      pure (.Call (← resolveOperand f) (← (args.mapM fun a => (resolveSpanned a))) (← resolvePlace p) b u s span)
    | .TailCall f args span =>
      checkSpan ctx span.id
      pure (.TailCall (← resolveOperand f) (← (args.mapM fun a => (resolveSpanned a))) span)
    | .Assert o e a b u => pure (.Assert (← resolveOperand o) e (← resolveAssert a) b u)
    | .Yield o b p d => pure (.Yield (← resolveOperand o) b (← resolvePlace p) d)
    | .CoroutineDrop => pure .CoroutineDrop
    | .FalseEdge r i => pure (.FalseEdge r i)
    | .FalseUnwind r u => pure (.FalseUnwind r u)
    | .InlineAsm a => pure (.InlineAsm (← resolveAsm a))
  pure ⟨t.sourceInfo, kind⟩

private def unwindTargets : MIR.UnwindAction → Array Nat
  | .Cleanup target => #[target]
  | .Continue | .Unreachable | .Terminate _ => #[]
private def controlTargets : MIR.TerminatorKind → Array Nat
  | .Goto target _ => #[target]
  | .SwitchInt _ targets => targets.cases.map (fun (.Case _ target) => target) ++ #[targets.otherwise]
  | .Drop _ target unwind _ asyncDrop => #[target] ++ unwindTargets unwind ++ asyncDrop.toArray
  | .Call _ _ _ target unwind _ _ => target.toArray ++ unwindTargets unwind
  | .Assert _ _ _ target unwind => #[target] ++ unwindTargets unwind
  | .Yield _ resume _ drop => #[resume] ++ drop.toArray
  | .FalseEdge real imaginary => #[real, imaginary]
  | .FalseUnwind real unwind => #[real] ++ unwindTargets unwind
  | .InlineAsm asm => asm.targets ++ unwindTargets asm.unwind
  | .UnwindResume | .UnwindTerminate _ | .Return | .Unreachable | .TailCall .. | .CoroutineDrop => #[]

def parseBody (sourcePath : String) : JsonReader.Parser (DraftBody) := do
  return { (← parseBodyRaw) with sourcePath }

def resolveBody (ctx : Context) (d : DraftBody) : Result Body := do
  let ctx : Context := { ctx with
    localCount := d.locals.size
    blockCount := d.blocks.size
    scopeCount := d.sourceScopes.size }
  unless !d.blocks.isEmpty do throw "body has no entry basic block"
  for (scope, index) in d.sourceScopes.toList.zipIdx do
    unless scope.id == index do throw "noncontiguous source scopes"
    checkSpan ctx scope.spanId
    for parent in scope.parent.toArray ++ scope.inlinedParent.toArray do
      check parent ctx.scopeCount "parent source scope"
    if let some inlineScope := scope.inlined then checkSpan ctx inlineScope.callsiteSpanId
  for (decl, index) in d.locals.toList.zipIdx do
    unless decl.id == index do throw "noncontiguous local IDs"
    checkType ctx decl.typeId
    checkSpan ctx decl.sourceInfo.spanId
    check decl.sourceInfo.scope ctx.scopeCount "source scope"
  for backtrace in d.backtraceSpans do checkSpan ctx backtrace.spanId
  let mut blocks : Array MIR.BasicBlock := #[]
  let mut facts := #[]
  let mut evidence := #[]
  for block in d.blocks do
    let statements ← block.statements.mapM fun s => runFacts ctx (resolveStatement s)
    let (term, termFacts) ← runFacts ctx (resolveTerminator block.terminator)
    for target in controlTargets term.kind do check target ctx.blockCount "control-flow target"
    blocks := blocks.push ⟨statements.map Prod.fst, term, block.cleanup⟩
    facts := facts.push ((statements.map Prod.snd).push termFacts)
    evidence := evidence.push block.terminator.evidence
  unless d.argumentCount < ctx.localCount do throw "argument count exceeds locals"
  if let some index := d.spreadArgument then
    unless index > 0 && index ≤ d.argumentCount do throw "invalid spread argument"
  for id in d.definitionId do checkDef ctx id
  checkSpan ctx d.spanId
  checkSpan ctx d.preambleDefSpanId
  let requiredConsts ← d.requiredConsts.mapM (resolveConstOperand ctx)
  return {
    mir := ⟨d.phase, d.argumentCount, d.spreadArgument, d.locals.map (·.typeId), blocks⟩,
    definitionId := d.definitionId, defPath := d.defPath.getD d.sourcePath, sourcePath := d.sourcePath,
    spanId := d.spanId, preambleDefSpanId := d.preambleDefSpanId, injectionPhase := d.injectionPhase,
    instanceId := d.instanceId, localSources := d.locals.map (·.sourceInfo), sourceScopes := d.sourceScopes,
    backtraceSpans := d.backtraceSpans, callEvidence := evidence, nodeFacts := facts, requiredConsts,
    promotedBodies := d.promotedBodies }

def decodeGenericArgs (ctx : Context) (args : Array MIR.GenericArg) : Result (Array MIR.GenericArg) := do
  checkArgs ctx args
  pure args

def decodePlace (ctx : Context) (p : Draft.Place) : Result MIR.Place :=
  runResolve ctx (resolvePlace p)

end Miri.Input.DecodeMIR
