import Miri.Input.JsonReader
import Miri.Input.MIRParser
import Miri.Input.MIRLeaves
import Miri.Input.DecoderValues

namespace Miri.Input.DecodeMIR
open JsonReader Miri.MIR
open Std.Internal.Parsec Std.Internal.Parsec.String
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
  size_bytes : Option Nat := none
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
  | "size_bytes" => return {s with size_bytes := some (← natural)}
  | "allocation" => return {s with allocation := some (← natural)}
  | "offset_bytes" => return {s with offset_bytes := some (← natural)}
  | "immutable" => return {s with immutable := some (← boolean)}
  | "shared_ref" => return {s with shared_ref := some (← boolean)}
  | "address" => return {s with address := some (← number)}
  | "address_width_bytes" => return {s with address_width_bytes := some (← natural)}
  | "metadata_length" => return {s with metadata_length := some (← natural)}
  | _ => skipValue; pure s
def finishConstValueFields (s : ConstValueFields) : JsonReader.Parser (MIR.ConstValue) := do
  let discriminator ← required s.kind "kind"
  let allowed : List String := match discriminator with
    | "zero_sized" => ["kind"]
    | "scalar" => ["kind", "bits_unsigned", "size_bytes"]
    | "pointer_scalar" => ["kind", "allocation", "offset_bytes", "immutable", "shared_ref"]
    | "pointer_scalar_without_provenance" => ["kind", "address", "address_width_bytes"]
    | "slice_allocation" => ["kind", "allocation", "metadata_length"]
    | "indirect_allocation" => ["kind", "allocation", "offset_bytes"]
    | _ => ["kind"]
  rejectIncompatible allowed [("kind", s.kind.isSome), ("bits_unsigned", s.bits_unsigned.isSome), ("size_bytes", s.size_bytes.isSome), ("allocation", s.allocation.isSome), ("offset_bytes", s.offset_bytes.isSome), ("immutable", s.immutable.isSome), ("shared_ref", s.shared_ref.isSome), ("address", s.address.isSome), ("address_width_bytes", s.address_width_bytes.isSome), ("metadata_length", s.metadata_length.isSome)]
  match (← required s.kind "kind") with
  | "zero_sized" => pure .ZeroSized
  | "scalar" =>
    let bits ← required s.bits_unsigned "bits_unsigned"
    let size ← required s.size_bytes "size_bytes"
    unless size > 0 && bits < 2 ^ (8 * size) do reject "scalar bits exceed byte width"
    pure (.Scalar (.Int bits size))
  | "pointer_scalar" => pure (.Scalar (.Ptr (.Allocation (← required s.allocation "allocation") (← required s.offset_bytes "offset_bytes") (← required s.immutable "immutable") (← required s.shared_ref "shared_ref"))))
  | "pointer_scalar_without_provenance" => pure (.Scalar (.Ptr (.Address (← required s.address "address") (← required s.address_width_bytes "address_width_bytes"))))
  | "slice_allocation" => pure (.Slice (← required s.allocation "allocation") (← required s.metadata_length "metadata_length"))
  | "indirect_allocation" => pure (.Indirect (← required s.allocation "allocation") (← required s.offset_bytes "offset_bytes"))
  | _ => reject "unknown or unavailable evaluated constant"
def parseConstValue : JsonReader.Parser (MIR.ConstValue) := do
  finishConstValueFields (← object {} parseConstValueField)
structure ParseEvaluatedFields where
  kind : Option (String) := none
  value : Option (MIR.ConstValue) := none

def parseEvaluatedField (s : ParseEvaluatedFields) (key : String) : JsonReader.Parser (ParseEvaluatedFields) := do
  match key with
  | "kind" => return {s with kind := some (← string)}
  | "value" => return {s with value := some (← parseConstValue)}
  | _ => skipValue; pure s
def finishParseEvaluatedFields (s : ParseEvaluatedFields) : JsonReader.Parser (MIR.ConstValue) := do
  unless (← required s.kind "kind") == "evaluated_const" do reject "unknown constant evaluation record"
  required s.value "value"
def parseEvaluated : JsonReader.Parser (MIR.ConstValue) := do
  finishParseEvaluatedFields (← object {} parseEvaluatedField)
open MIRParser

structure ParseConstOperandFields where
  type : Option (Nat) := none
  span : Option (Nat) := none
  user_type_annotation : Option (Option Nat) := none
  constant : Option (MIR.ConstValue) := none

def parseConstOperandField (s : ParseConstOperandFields) (key : String) : MIRParser.Parser (ParseConstOperandFields) := do
  match key with
  | "type" => return {s with type := some (← (do let id ← natural; recordType id; pure id))}
  | "span" => return {s with span := some (← (do let id ← natural; recordSpan id; pure id))}
  | "user_type_annotation" => return {s with user_type_annotation := some (← MIRParser.nullable annotation)}
  | "constant" => return {s with constant := some (← parseEvaluated)}
  | _ => skipValue; pure s
def finishParseConstOperandFields (s : ParseConstOperandFields) : MIRParser.Parser MIR.ConstOperand := do
  makeConstant (← required s.type "type") ⟨(← required s.span "span")⟩
    (← required s.user_type_annotation "user_type_annotation") (← required s.constant "constant")
def parseConstOperand : MIRParser.Parser MIR.ConstOperand := do
  finishParseConstOperandFields (← MIRParser.object {} parseConstOperandField)
structure RuntimeCheckFields where
  kind : Option (String) := none
  enabled : Option (Bool) := none

def runtimeCheckField (s : RuntimeCheckFields) (key : String) : MIRParser.Parser (RuntimeCheckFields) := do
  match key with
  | "kind" => return {s with kind := some (← string)}
  | "enabled" => return {s with enabled := some (← boolean)}
  | _ => skipValue; pure s
def finishRuntimeCheckFields (s : RuntimeCheckFields) : MIRParser.Parser (MIR.RuntimeChecks) := do
  let _ ← required s.enabled "enabled"
  match (← required s.kind "kind") with
  | "ub_checks" => pure .UbChecks
  | "contract_checks" => pure .ContractChecks
  | "overflow_checks" => pure .OverflowChecks
  | _ => reject "unknown runtime check"
def runtimeCheck : MIRParser.Parser (MIR.RuntimeChecks) := do
  finishRuntimeCheckFields (← MIRParser.object {} runtimeCheckField)
structure OperandFields where
  kind : Option (String) := none
  place : Option (ParsedPlace) := none
  constant : Option (MIR.ConstOperand) := none
  check : Option (MIR.RuntimeChecks) := none

def operandField (s : OperandFields) (key : String) : MIRParser.Parser (OperandFields) := do
  match key with
  | "kind" => return {s with kind := some (← string)}
  | "place" => return {s with place := some (← parsedPlace)}
  | "constant" => return {s with constant := some (← parseConstOperand)}
  | "check" => return {s with check := some (← runtimeCheck)}
  | _ => skipValue; pure s
def finishOperandFields (s : OperandFields) : MIRParser.Parser (ParsedOperand) := do
  let discriminator ← required s.kind "kind"
  let allowed : List String := match discriminator with
    | "Copy" => ["kind", "place"]
    | "Move" => ["kind", "place"]
    | "Constant" => ["kind", "constant"]
    | "RuntimeChecks" => ["kind", "check"]
    | _ => ["kind"]
  rejectIncompatible allowed [("kind", s.kind.isSome), ("place", s.place.isSome), ("constant", s.constant.isSome), ("check", s.check.isSome)]
  match (← required s.kind "kind") with
  | "Copy" => do
    let p ← required s.place "place"
    pure ⟨.Copy p.value, some p.typeId⟩
  | "Move" => do
    let p ← required s.place "place"
    pure ⟨.Move p.value, some p.typeId⟩
  | "Constant" => do
    let c ← required s.constant "constant"
    pure ⟨.Constant c, constantType c⟩
  | "RuntimeChecks" => pure ⟨.RuntimeChecks (← required s.check "check"), none⟩
  | _ => reject "unknown operand"
def operand : MIRParser.Parser (ParsedOperand) := do
  finishOperandFields (← MIRParser.object {} operandField)
structure WithRetagFields where
  kind : Option (String) := none
  performs_retag : Option (Bool) := none

def withRetagField (s : WithRetagFields) (key : String) : MIRParser.Parser (WithRetagFields) := do
  match key with
  | "kind" => return {s with kind := some (← string)}
  | "performs_retag" => return {s with performs_retag := some (← boolean)}
  | _ => skipValue; pure s
def finishWithRetagFields (s : WithRetagFields) : MIRParser.Parser (MIR.WithRetag) := do
  let k ← required s.kind "kind"
  unless (← required s.performs_retag "performs_retag") == (k == "yes") do reject "WithRetag boolean disagrees with tag"
  match k with
  | "yes" => pure .Yes
  | "no" => pure .No
  | _ => reject "unknown retag mode"
def withRetag : MIRParser.Parser (MIR.WithRetag) := do
  finishWithRetagFields (← MIRParser.object {} withRetagField)
structure TlsInitializerFields where
  allocation : Option (AllocationMemory) := none

def tlsInitializerField (s : TlsInitializerFields) (key : String) : MIRParser.Parser (TlsInitializerFields) := do
  match key with
  | "allocation" =>
    let allocation ← match (← get).pools with
      | none => DecoderValues.parseAllocationMemoryInline "$thread_local.initializer.allocation"
      | some pools => DecoderValues.parseAllocationMemory "$thread_local.initializer.allocation" pools.initializationRanges pools.relocations
    return {s with allocation := some allocation}
  | _ => skipValue; pure s
def finishTlsInitializerFields (s : TlsInitializerFields) : MIRParser.Parser (Option AllocationMemory) := do
  pure s.allocation
def tlsInitializer : MIRParser.Parser (Option AllocationMemory) := do
  finishTlsInitializerFields (← MIRParser.object {} tlsInitializerField)
private def enumTag : MIRParser.Parser (String) := do
  if (← (peek! : JsonReader.Parser Char)) == '"' then string
  else
    let value ← MIRParser.object (none : Option String) fun state key => do
      if key == "kind" then return some (← string)
      else skipValue; pure state
    required value "kind"

private def rawPointer : MIRParser.Parser (MIR.RawPtrKind) := do
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
  operand : Option (ParsedOperand) := none
  left : Option (ParsedOperand) := none
  right : Option (ParsedOperand) := none
  operands : Option (Array ParsedOperand) := none
  retag : Option (MIR.WithRetag) := none
  operator : Option (String) := none
  place : Option (ParsedPlace) := none
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

def rvalueField (s : RvalueFields) (key : String) : MIRParser.Parser (RvalueFields) := do
  match key with
  | "kind" => return {s with kind := some (← string)}
  | "operand" => return {s with operand := some (← operand)}
  | "left" => return {s with left := some (← operand)}
  | "right" => return {s with right := some (← operand)}
  | "operands" => return {s with operands := some (← MIRParser.array operand)}
  | "retag" => return {s with retag := some (← withRetag)}
  | "operator" => return {s with operator := some (← enumTag)}
  | "place" => return {s with place := some (← parsedPlace)}
  | "type" => return {s with type := some (← (do let id ← natural; recordType id; pure id))}
  | "target_type" => return {s with target_type := some (← (do let id ← natural; recordType id; pure id))}
  | "count" => return {s with count := some (← natural)}
  | "region" =>
    let value ← GenericArgsCodec.region
    recordRegion value
    return {s with region := some value}
  | "borrow_kind" => return {s with borrow_kind := some (← borrow)}
  | "pointer_kind" => return {s with pointer_kind := some (← rawPointer)}
  | "cast_kind" => return {s with cast_kind := some (← castKind)}
  | "aggregate_kind" =>
    let value ← aggregate
    recordAggregate value
    return {s with aggregate_kind := some value}
  | "mutability" => return {s with mutability := some (← mutability)}
  | "def_id" => return {s with def_id := some (← (do let id ← natural; recordDef id; pure id))}
  | "global_info" => return {s with global_info := some (← DecoderValues.decodeStaticGlobalInfo)}
  | "initializer" => return {s with initializer := some (← tlsInitializer)}
  | "vtable_allocation" => return {s with vtable_allocation := some (← upcast)}
  | _ => skipValue; pure s
def finishRvalueFields (s : RvalueFields) : MIRParser.Parser (MIR.Rvalue) := do
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
  | "Repeat" =>
    let count ← required s.count "count"
    recordTypeConstant count
    pure (.Repeat (← required s.operand "operand") count)
  | "Ref" => pure (.Ref (← required s.region "region") (← required s.borrow_kind "borrow_kind") (← required s.place "place"))
  | "ThreadLocalRef" =>
    let info ← required s.global_info "global_info"
    unless info.isStatic && info.threadLocal do reject "TLS declaration compiler query evidence is unresolved or inconsistent"
    let initializer ← required s.initializer "initializer"
    if !info.foreignItem && initializer.isNone then reject "missing TLS initializer allocation"
    if info.foreignItem && initializer.isSome then reject "foreign TLS declaration cannot carry an initializer allocation"
    let definition ← required s.def_id "def_id"
    modify fun s => {s with facts.threadLocals := s.facts.threadLocals.push ⟨definition, info, initializer⟩}
    pure (.ThreadLocalRef definition)
  | "RawPtr" => pure (.RawPtr (← required s.pointer_kind "pointer_kind") (← required s.place "place"))
  | "Cast" =>
    let kind ← required s.cast_kind "cast_kind"
    let desc := s.vtable_allocation.join
    if desc.isSome then
      match kind with
      | .PointerCoercion .Unsize _ => pure ()
      | _ => reject "dynamic vtable descriptor requires an unsizing cast"
    let operand ← required s.operand "operand"
    let target ← required s.target_type "target_type"
    if let some desc := desc then
      let some operandType := operand.typeId | reject "dynamic vtable upcast lacks operand type"
      let desc := {desc with operandType, castTarget := target}
      for id in #[desc.operandType, desc.castTarget, desc.sourceType, desc.targetType,
          desc.sourcePointeeType, desc.targetPointeeType, desc.sourceTailType, desc.targetTailType,
          desc.querySource, desc.queryTarget] do recordType id
      modify fun s => {s with facts.dynamicUpcasts := s.facts.dynamicUpcasts.push desc}
    pure (.Cast kind operand.value target)
  | "Aggregate" => pure (.Aggregate (← required s.aggregate_kind "aggregate_kind") ((← required s.operands "operands").map (·.value)))
  | "Reborrow" => pure (.Reborrow (← required s.type "type") (← required s.mutability "mutability") (← required s.place "place"))
  | _ => reject "unknown rvalue"
def rvalue : MIRParser.Parser (MIR.Rvalue) := do
  finishRvalueFields (← MIRParser.object {} rvalueField)
structure StatementKindFields where
  variant : Option (String) := none
  place : Option (ParsedPlace) := none
  rvalue : Option (MIR.Rvalue) := none
  «local» : Option (Nat) := none
  variant_index : Option (Nat) := none
  cause : Option (MIR.FakeReadCause) := none
  user_type_projection : Option (MIR.UserTypeProjection) := none
  variance : Option (MIR.Variance) := none
  coverage : Option (MIR.CoverageKind) := none
  intrinsic : Option (String) := none
  value : Option (ParsedOperand) := none
  src : Option (ParsedOperand) := none
  dst : Option (ParsedOperand) := none
  count : Option (ParsedOperand) := none
  reason : Option (String) := none

def statementKindField (s : StatementKindFields) (key : String) : MIRParser.Parser (StatementKindFields) := do
  match key with
  | "variant" => return {s with variant := some (← string)}
  | "place" => return {s with place := some (← parsedPlace)}
  | "rvalue" => return {s with rvalue := some (← rvalue)}
  | "local" => return {s with «local» := some (← (do let id ← natural; recordLocal id; pure id))}
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
def finishStatementKindFields (s : StatementKindFields) : MIRParser.Parser (MIR.StatementKind) := do
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
  | "FakeRead" =>
    let cause ← required s.cause "cause"
    match cause with
    | .ForMatchedPlace (some id) | .ForLet (some id) => recordDef id
    | _ => pure ()
    pure (.FakeRead cause (← required s.place "place"))
  | "AscribeUserType" => pure (.AscribeUserType (← required s.place "place") (← required s.user_type_projection "user_type_projection") (← required s.variance "variance"))
  | "Coverage" =>
    let coverage ← required s.coverage "coverage"
    match coverage with
    | .Point _ hir => recordDef hir.owner
    | _ => pure ()
    pure (.Coverage coverage)
  | "Intrinsic" =>
    match (← required s.intrinsic "intrinsic") with
    | "Assume" => pure (.Intrinsic (.Assume (← required s.value "value")))
    | "CopyNonOverlapping" => pure (.Intrinsic (.CopyNonOverlapping ⟨(← required s.src "src"), (← required s.dst "dst"), (← required s.count "count")⟩))
    | _ => reject "unknown nondiverging intrinsic"
  | "BackwardIncompatibleDropHint" =>
    unless (← required s.reason "reason") == "edition_2024" do reject "unknown backward drop reason"
    pure (.BackwardIncompatibleDropHint (← required s.place "place") .Edition2024)
  | _ => reject "unknown statement"
def statementKind : MIRParser.Parser (MIR.StatementKind) := do
  finishStatementKindFields (← MIRParser.object {} statementKindField)
private def sharedSource : MIRParser.Parser MIR.SourceInfo := do
  match (← get).pools with
  | none => source
  | some pools =>
    let id ← natural
    let some value := pools.sources[id]? | reject s!"source_infos: unresolved source info {id}"
    pure ⟨⟨value.spanId⟩, value.scope⟩

private def sharedSourceInfo : MIRParser.Parser Input.SourceInfo := do
  let value ← sharedSource
  pure ⟨value.span.id, value.scope⟩

private def mergeBound (a b : Option Nat) : Option Nat :=
  match a, b with
  | none, b => b
  | a, none => a
  | some a, some b => some (max a b)

private def sharedStatement : MIRParser.Parser MIR.StatementKind := do
  match (← get).pools with
  | none => statementKind
  | some pools =>
    let id ← natural
    let some entry := pools.statements[id]? | reject s!"statement_kinds: unresolved statement kind {id}"
    modify fun state => {state with
      references := {
        types := mergeBound state.references.types entry.references.types
        allocations := mergeBound state.references.allocations entry.references.allocations
        definitions := mergeBound state.references.definitions entry.references.definitions
        typeConstants := mergeBound state.references.typeConstants entry.references.typeConstants
        spans := mergeBound state.references.spans entry.references.spans
        scalarWidths := state.references.scalarWidths ++ entry.references.scalarWidths }
      facts := {
        places := state.facts.places ++ entry.facts.places
        constantAllocations := state.facts.constantAllocations ++ entry.facts.constantAllocations
        threadLocals := state.facts.threadLocals ++ entry.facts.threadLocals
        dynamicUpcasts := state.facts.dynamicUpcasts ++ entry.facts.dynamicUpcasts }
      locals := mergeBound state.locals entry.locals
      blocks := mergeBound state.blocks entry.blocks
      scopes := mergeBound state.scopes entry.scopes }
    pure entry.value

structure StatementFields where
  source_info : Option (MIR.SourceInfo) := none
  kind : Option (MIR.StatementKind) := none

def statementField (s : StatementFields) (key : String) : MIRParser.Parser (StatementFields) := do
  match key with
  | "source_info" => return {s with source_info := some (← sharedSource)}
  | "kind" => return {s with kind := some (← sharedStatement)}
  | _ => skipValue; pure s
def finishStatementFields (s : StatementFields) : MIRParser.Parser (MIR.Statement) := do
  let source ← required s.source_info "source_info"
  recordSource source
  return ⟨source, (← required s.kind "kind")⟩
def statement : MIRParser.Parser (MIR.Statement × NodeFacts) := do
  modify fun s => {s with facts := {}}
  let value ← finishStatementFields (← MIRParser.object {} statementField)
  return (value, (← get).facts)
structure AssertKindFields where
  kind : Option (String) := none
  operator : Option (MIR.BinOp) := none
  left : Option (ParsedOperand) := none
  right : Option (ParsedOperand) := none
  length : Option (ParsedOperand) := none
  index : Option (ParsedOperand) := none
  operand : Option (ParsedOperand) := none
  required : Option (ParsedOperand) := none
  found : Option (ParsedOperand) := none
  coroutine_kind : Option (MIR.CoroutineKind) := none

def assertKindField (s : AssertKindFields) (key : String) : MIRParser.Parser (AssertKindFields) := do
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
def finishAssertKindFields (s : AssertKindFields) : MIRParser.Parser (MIR.AssertKind) := do
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
def assertKind : MIRParser.Parser (MIR.AssertKind) := do
  finishAssertKindFields (← MIRParser.object {} assertKindField)
structure SpannedOperandFields where
  span : Option (Nat) := none
  operand : Option (ParsedOperand) := none

def spannedOperandField (s : SpannedOperandFields) (key : String) : MIRParser.Parser (SpannedOperandFields) := do
  match key with
  | "span" => return {s with span := some (← (do let id ← natural; recordSpan id; pure id))}
  | "operand" => return {s with operand := some (← operand)}
  | _ => skipValue; pure s
def finishSpannedOperandFields (s : SpannedOperandFields) : MIRParser.Parser (MIR.SpannedOperand) := do
  return ⟨⟨(← required s.span "span")⟩, (← required s.operand "operand")⟩
def spannedOperand : MIRParser.Parser (MIR.SpannedOperand) := do
  finishSpannedOperandFields (← MIRParser.object {} spannedOperandField)
/-- The `value` member in inline assembly is an operand for `in`, but a
constant operand for `const` and `sym_fn`. Both are parsed forward into this
schema-specific union before the enclosing tag is inspected. -/
private structure AsmConstantFields where
  kind : Option String := none
  value : Option MIR.ConstValue := none
  type : Option Nat := none
  span : Option Nat := none
  user_type_annotation : Option (Option Nat) := none
  constant : Option (MIR.ConstValue) := none

private def asmConstant : MIRParser.Parser ((Sum (MIR.ConstValue) MIR.ConstOperand)) := do
  let s ← MIRParser.object ({} : AsmConstantFields) fun s key => do
    match key with
    | "kind" => return {s with kind := some (← string)}
    | "value" => return {s with value := some (← parseConstValue)}
    | "type" => return {s with type := some (← (do let id ← natural; recordType id; pure id))}
    | "span" => return {s with span := some (← (do let id ← natural; recordSpan id; pure id))}
    | "user_type_annotation" => return {s with user_type_annotation := some (← MIRParser.nullable annotation)}
    | "constant" => return {s with constant := some (← parseEvaluated)}
    | _ => skipValue; pure s
  match s.kind with
  | some "evaluated_const" =>
    return .inl (← required s.value "value")
  | none =>
    let c ← required s.constant "constant"
    return .inr (← makeConstant (← required s.type "type") ⟨(← required s.span "span")⟩
      (← required s.user_type_annotation "user_type_annotation") c)
  | _ => reject "unknown assembly constant record"

structure AsmValueFields where
  kind : Option String := none
  place : Option ParsedPlace := none
  constant : Option (Sum (MIR.ConstValue) MIR.ConstOperand) := none
  check : Option MIR.RuntimeChecks := none
  type : Option Nat := none
  span : Option Nat := none
  user_type_annotation : Option (Option Nat) := none

def asmValueField (s : AsmValueFields) (key : String) : MIRParser.Parser (AsmValueFields) := do
  match key with
  | "kind" => return {s with kind := some (← string)}
  | "place" => return {s with place := some (← parsedPlace)}
  | "constant" => return {s with constant := some (← asmConstant)}
  | "check" => return {s with check := some (← runtimeCheck)}
  | "type" => return {s with type := some (← (do let id ← natural; recordType id; pure id))}
  | "span" => return {s with span := some (← (do let id ← natural; recordSpan id; pure id))}
  | "user_type_annotation" => return {s with user_type_annotation := some (← MIRParser.nullable annotation)}
  | _ => skipValue; pure s
def finishAsmValueFields (s : AsmValueFields) : MIRParser.Parser ParsedOperand := do
  match s.kind with
  | some "Copy" =>
    let p ← required s.place "place"
    pure ⟨.Copy p.value, some p.typeId⟩
  | some "Move" =>
    let p ← required s.place "place"
    pure ⟨.Move p.value, some p.typeId⟩
  | some "RuntimeChecks" => pure ⟨.RuntimeChecks (← required s.check "check"), none⟩
  | some "Constant" =>
    let .inr c ← required s.constant "constant" | reject "expected assembly constant operand"
    pure ⟨.Constant c, constantType c⟩
  | none =>
    let .inl c ← required s.constant "constant" | reject "expected assembly evaluated constant"
    let c ← makeConstant (← required s.type "type") ⟨(← required s.span "span")⟩
      (← required s.user_type_annotation "user_type_annotation") c
    pure ⟨.Constant c, constantType c⟩
  | _ => reject "unknown inline assembly input operand"
def asmValue : MIRParser.Parser (ParsedOperand) := do
  finishAsmValueFields (← MIRParser.object {} asmValueField)
structure AsmOperandFields where
  kind : Option (String) := none
  register : Option (MIR.InlineAsmRegOrRegClass) := none
  value : Option (ParsedOperand) := none
  late : Option (Bool) := none
  place : Option (Option ParsedPlace) := none
  input : Option (ParsedOperand) := none
  output : Option (Option ParsedPlace) := none
  def_id : Option (Nat) := none
  target_index : Option (Nat) := none

def asmOperandField (s : AsmOperandFields) (key : String) : MIRParser.Parser (AsmOperandFields) := do
  match key with
  | "kind" => return {s with kind := some (← string)}
  | "register" => return {s with register := some (← asmRegister)}
  | "value" => return {s with value := some (← asmValue)}
  | "late" => return {s with late := some (← boolean)}
  | "place" => return {s with place := some (← MIRParser.nullable parsedPlace)}
  | "input" => return {s with input := some (← operand)}
  | "output" => return {s with output := some (← MIRParser.nullable parsedPlace)}
  | "def_id" => return {s with def_id := some (← (do let id ← natural; recordDef id; pure id))}
  | "target_index" => return {s with target_index := some (← natural)}
  | _ => skipValue; pure s
def finishAsmOperandFields (s : AsmOperandFields) : MIRParser.Parser (MIR.InlineAsmOperand) := do
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
  | "out" => pure (.Out (← required s.register "register") (← required s.late "late") ((← required s.place "place").map (·.value)))
  | "inout" => pure (.InOut (← required s.register "register") (← required s.late "late") (← required s.input "input") ((← required s.output "output").map (·.value)))
  | "const" | "sym_fn" =>
    let .Constant c := (← required s.value "value").value | reject "expected assembly constant"
    if (← required s.kind "kind") == "const" then pure (.Const c) else pure (.SymFn c)
  | "sym_static" => pure (.SymStatic (← required s.def_id "def_id"))
  | "label" => pure (.Label (← required s.target_index "target_index"))
  | _ => reject "unknown assembly operand"
def asmOperand : MIRParser.Parser (MIR.InlineAsmOperand) := do
  finishAsmOperandFields (← MIRParser.object {} asmOperandField)
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

def asmOptionsField (s : AsmOptionsFields) (key : String) : MIRParser.Parser (AsmOptionsFields) := do
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
def finishAsmOptionsFields (s : AsmOptionsFields) : MIRParser.Parser (MIR.InlineAsmOptions) := do
  return ⟨(← required s.pure "pure"), (← required s.nomem "nomem"), (← required s.readonly "readonly"), (← required s.preserves_flags "preserves_flags"), (← required s.noreturn "noreturn"), (← required s.nostack "nostack"), (← required s.att_syntax "att_syntax"), (← required s.raw "raw"), (← required s.may_unwind "may_unwind")⟩
def asmOptions : MIRParser.Parser (MIR.InlineAsmOptions) := do
  finishAsmOptionsFields (← MIRParser.object {} asmOptionsField)
structure SwitchTargetFields where
  value : Option (Nat) := none
  target : Option (Nat) := none

def switchTargetField (s : SwitchTargetFields) (key : String) : MIRParser.Parser (SwitchTargetFields) := do
  match key with
  | "value" => return {s with value := some (← number)}
  | "target" => return {s with target := some (← natural)}
  | _ => skipValue; pure s
def finishSwitchTargetFields (s : SwitchTargetFields) : MIRParser.Parser (MIR.SwitchTarget) := do
  return .Case (← required s.value "value") (← required s.target "target")
def switchTarget : MIRParser.Parser (MIR.SwitchTarget) := do
  finishSwitchTargetFields (← MIRParser.object {} switchTargetField)
inductive DraftTarget where
  | case (value : MIR.SwitchTarget)
  | block (value : Nat)
private def targetItem : MIRParser.Parser (DraftTarget) := do
  if (← (peek! : JsonReader.Parser Char)) == '{' then .case <$> switchTarget
  else .block <$> natural

structure TerminatorKindFields where
  variant : Option (String) := none
  condition : Option (ParsedOperand) := none
  expected : Option (Bool) := none
  message : Option (MIR.AssertKind) := none
  target : Option (Option Nat) := none
  unwind : Option (MIR.UnwindAction) := none
  real_target : Option (Nat) := none
  imaginary_target : Option (Nat) := none
  loop_hints : Option (Array MIR.LoopHintAttr) := none
  discriminant : Option (ParsedOperand) := none
  targets : Option (Array DraftTarget) := none
  otherwise : Option (Nat) := none
  reason : Option (MIR.UnwindTerminateReason) := none
  place : Option (ParsedPlace) := none
  replace : Option (Bool) := none
  async_drop : Option (Option Nat) := none
  function : Option (ParsedOperand) := none
  args : Option (Array MIR.SpannedOperand) := none
  destination : Option (ParsedPlace) := none
  call_source : Option (MIR.CallSource) := none
  function_span : Option (Nat) := none
  value : Option (ParsedOperand) := none
  resume : Option (Nat) := none
  resume_arg : Option (ParsedPlace) := none
  drop : Option (Option Nat) := none
  resolution : Option (CallResolutionEvidence) := none
  asm_macro : Option (String) := none
  options : Option (MIR.InlineAsmOptions) := none
  template : Option (Array MIR.InlineAsmTemplatePiece) := none
  operands : Option (Array MIR.InlineAsmOperand) := none
  line_spans : Option (Array Nat) := none

def terminatorKindField (s : TerminatorKindFields) (key : String) : MIRParser.Parser (TerminatorKindFields) := do
  match key with
  | "variant" => return {s with variant := some (← string)}
  | "condition" => return {s with condition := some (← operand)}
  | "expected" => return {s with expected := some (← boolean)}
  | "message" => return {s with message := some (← assertKind)}
  | "target" => return {s with target := some (← MIRParser.nullable natural)}
  | "unwind" => return {s with unwind := some (← unwind)}
  | "real_target" => return {s with real_target := some (← natural)}
  | "imaginary_target" => return {s with imaginary_target := some (← natural)}
  | "loop_hints" => return {s with loop_hints := some (← MIRParser.array loopHint)}
  | "discriminant" => return {s with discriminant := some (← operand)}
  | "targets" => return {s with targets := some (← MIRParser.array targetItem)}
  | "otherwise" => return {s with otherwise := some (← natural)}
  | "reason" => return {s with reason := some (← unwindReason)}
  | "place" => return {s with place := some (← parsedPlace)}
  | "replace" => return {s with replace := some (← boolean)}
  | "async_drop" => return {s with async_drop := some (← MIRParser.nullable natural)}
  | "function" => return {s with function := some (← operand)}
  | "args" => return {s with args := some (← MIRParser.array spannedOperand)}
  | "destination" => return {s with destination := some (← parsedPlace)}
  | "call_source" => return {s with call_source := some (← callSource)}
  | "function_span" => return {s with function_span := some (← (do let id ← natural; recordSpan id; pure id))}
  | "value" => return {s with value := some (← operand)}
  | "resume" => return {s with resume := some (← natural)}
  | "resume_arg" => return {s with resume_arg := some (← parsedPlace)}
  | "drop" => return {s with drop := some (← MIRParser.nullable natural)}
  | "resolution" => return {s with resolution := some (← callEvidence)}
  | "asm_macro" => return {s with asm_macro := some (← string)}
  | "options" => return {s with options := some (← asmOptions)}
  | "template" => return {s with template := some (← MIRParser.array asmPiece)}
  | "operands" => return {s with operands := some (← MIRParser.array asmOperand)}
  | "line_spans" => return {s with line_spans := some (← MIRParser.array natural)}
  | _ => skipValue; pure s
def finishTerminatorKindFields (s : TerminatorKindFields) : MIRParser.Parser (MIR.TerminatorKind × Option CallResolutionEvidence) := do
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
    | "Return" => pure MIR.TerminatorKind.Return
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
      for span in (← required s.line_spans "line_spans") do recordSpan span
      for piece in template do
        match piece with
        | .Placeholder _ _ span => recordSpan span.id
        | _ => pure ()
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
def terminatorKind : MIRParser.Parser (MIR.TerminatorKind × Option CallResolutionEvidence) := do
  finishTerminatorKindFields (← MIRParser.object {} terminatorKindField)
structure TerminatorFields where
  source_info : Option (MIR.SourceInfo) := none
  kind : Option (MIR.TerminatorKind × Option CallResolutionEvidence) := none

def terminatorField (s : TerminatorFields) (key : String) : MIRParser.Parser (TerminatorFields) := do
  match key with
  | "source_info" => return {s with source_info := some (← sharedSource)}
  | "kind" => return {s with kind := some (← terminatorKind)}
  | _ => skipValue; pure s
def finishTerminatorFields (s : TerminatorFields) : MIRParser.Parser (MIR.Terminator × Option CallResolutionEvidence) := do
  let pair ← required s.kind "kind"
  let source ← required s.source_info "source_info"
  recordSource source
  for e in pair.2 do
    for ty in e.functionType do recordType ty
  return (⟨source, pair.1⟩, pair.2)
def terminator : MIRParser.Parser (MIR.Terminator × NodeFacts × Option CallResolutionEvidence) := do
  modify fun s => {s with facts := {}}
  let (value, evidence) ← finishTerminatorFields (← MIRParser.object {} terminatorField)
  return (value, (← get).facts, evidence)
structure BasicBlockFields where
  block : Option (Nat) := none
  statements : Option (Array (MIR.Statement × NodeFacts)) := none
  terminator : Option (MIR.Terminator × NodeFacts × Option CallResolutionEvidence) := none
  is_cleanup : Option (Bool) := none

def basicBlockField (s : BasicBlockFields) (key : String) : MIRParser.Parser (BasicBlockFields) := do
  match key with
  | "block" => return {s with block := some (← natural)}
  | "statements" => return {s with statements := some (← MIRParser.array statement)}
  | "terminator" => return {s with terminator := some (← terminator)}
  | "is_cleanup" => return {s with is_cleanup := some (← boolean)}
  | _ => skipValue; pure s
def finishBasicBlockFields (s : BasicBlockFields) : MIRParser.Parser (Nat × ParsedBlock) := do
  let statements ← required s.statements "statements"
  let (term, facts, evidence) ← required s.terminator "terminator"
  recordTargets term.kind
  return ((← required s.block "block"), ⟨⟨statements.map Prod.fst, term, (← required s.is_cleanup "is_cleanup")⟩, (statements.map Prod.snd).push facts, evidence⟩)
def basicBlock : MIRParser.Parser (Nat × ParsedBlock) := do
  finishBasicBlockFields (← MIRParser.object {} basicBlockField)
structure LocalDeclFields where
  «local» : Option (Nat) := none
  type : Option (Nat) := none
  source_info : Option (Input.SourceInfo) := none

def localDeclField (s : LocalDeclFields) (key : String) : MIRParser.Parser (LocalDeclFields) := do
  match key with
  | "local" => return {s with «local» := some (← (do let id ← natural; recordLocal id; pure id))}
  | "type" => return {s with type := some (← (do let id ← natural; recordType id; pure id))}
  | "source_info" => return {s with source_info := some (← sharedSourceInfo)}
  | _ => skipValue; pure s
def finishLocalDeclFields (s : LocalDeclFields) : MIRParser.Parser (LocalDecl) := do
  return ⟨(← required s.«local» "local"), (← required s.type "type"), (← required s.source_info "source_info")⟩
def localDecl : MIRParser.Parser (LocalDecl) := do
  finishLocalDeclFields (← MIRParser.object {} localDeclField)
structure PromotedBodyFields where
  promoted_index : Option (Option Nat) := none
  body : Option (Option Nat) := none

def promotedBodyField (s : PromotedBodyFields) (key : String) : MIRParser.Parser (PromotedBodyFields) := do
  match key with
  | "promoted_index" => return {s with promoted_index := some (← MIRParser.nullable natural)}
  | "body" => return {s with body := some (← MIRParser.nullable natural)}
  | _ => skipValue; pure s
def finishPromotedBodyFields (path : String) (s : PromotedBodyFields) : MIRParser.Parser (PromotedBody) := do
  let index := s.promoted_index.join.getD 0
  let bodyId := s.body.join
  if bodyId.isNone then
    reject s!"{path}[{index}]: promoted MIR body is absent; cannot import it as typed MIR"
  return ⟨index, bodyId⟩
def promotedBody (path : String) : MIRParser.Parser (PromotedBody) := do
  finishPromotedBodyFields path (← MIRParser.object {} promotedBodyField)
structure ParseBodyFields where
  phase : Option (MIR.MirPhase) := none
  arg_count : Option (Nat) := none
  spread_arg : Option (Option Nat) := none
  locals : Option (Array LocalDecl) := none
  basic_blocks : Option (Array (Nat × ParsedBlock)) := none
  def_id : Option (Option Nat) := none
  source_def_id : Option (Option Nat) := none
  def_path : Option (Option String) := none
  span : Option (Nat) := none
  preamble_def_span : Option (Nat) := none
  injection_phase : Option (Option MIR.MirPhase) := none
  instance_id : Option Nat := none
  source_scopes : Option (Array SourceScope) := none
  backtrace_spans : Option (Array BacktraceSpan) := none
  required_consts : Option (Array MIR.ConstOperand) := none
  promoted_bodies : Option (Array PromotedBody) := none

def parseBodyField (sourcePath : String) (s : ParseBodyFields) (key : String) : MIRParser.Parser (ParseBodyFields) := do
  match key with
  | "phase" => return {s with phase := some (← phase)}
  | "arg_count" => return {s with arg_count := some (← natural)}
  | "spread_arg" => return {s with spread_arg := some (← MIRParser.nullable natural)}
  | "locals" => return {s with locals := some (← MIRParser.array localDecl)}
  | "basic_blocks" => return {s with basic_blocks := some (← MIRParser.array basicBlock)}
  | "def_id" => return {s with def_id := some (← MIRParser.nullable natural)}
  | "source_def_id" => return {s with source_def_id := some (← MIRParser.nullable natural)}
  | "def_path" => return {s with def_path := some (← MIRParser.nullable string)}
  | "span" => return {s with span := some (← (do let id ← natural; recordSpan id; pure id))}
  | "preamble_def_span" => return {s with preamble_def_span := some (← natural)}
  | "injection_phase" => return {s with injection_phase := some (← MIRParser.nullable phase)}
  | "instance_id" => return {s with instance_id := some (← natural)}
  | "source_scopes" => return {s with source_scopes := some (← MIRParser.array scope)}
  | "backtrace_spans" =>
    let value ← match (← get).pools with
      | none => JsonReader.arrayIndexed (fun index => backtrace s!"{sourcePath}.backtrace_spans[{index}]")
      | some pools => do
        let id ← natural
        let some value := pools.backtraces[id]? | reject s!"{sourcePath}.backtrace_spans: unresolved backtrace {id}"
        pure value
    return {s with backtrace_spans := some value}
  | "required_consts" => return {s with required_consts := some (← MIRParser.array parseConstOperand)}
  | "promoted_bodies" => return {s with promoted_bodies := some (← MIRParser.array (promotedBody s!"{sourcePath}.promoted_bodies"))}
  | _ => skipValue; pure s
def finishParseBodyFields (sourcePath : String) (s : ParseBodyFields) : MIRParser.Parser Body := do
  let blocks ← required s.basic_blocks "basic_blocks"
  for (pair, index) in blocks.toList.zipIdx do
    unless pair.1 == index do reject "noncontiguous basic block IDs"
  let locals ← required s.locals "locals"
  let scopes ← required s.source_scopes "source_scopes"
  let argumentCount ← required s.arg_count "arg_count"
  let spreadArgument := s.spread_arg.join
  unless !blocks.isEmpty do reject "body has no entry basic block"
  unless argumentCount < locals.size do reject "argument count exceeds locals"
  if let some index := spreadArgument then
    unless index > 0 && index ≤ argumentCount do reject "invalid spread argument"
  for (scope, index) in scopes.toList.zipIdx do
    unless scope.id == index do reject "noncontiguous source scopes"
    recordSpan scope.spanId
    for parent in scope.parent.toArray ++ scope.inlinedParent.toArray do
      unless parent < scopes.size do reject s!"unresolved parent source scope {parent}"
    if let some inlineScope := scope.inlined then recordSpan inlineScope.callsiteSpanId
  for (decl, index) in locals.toList.zipIdx do
    unless decl.id == index do reject "noncontiguous local IDs"
    recordType decl.typeId
    recordSpan decl.sourceInfo.spanId
    recordScope decl.sourceInfo.scope
  let backtraceSpans ← required s.backtrace_spans "backtrace_spans"
  for backtrace in backtraceSpans do recordSpan backtrace.spanId
  let definitionId := s.def_id.join.orElse (fun _ => s.source_def_id.join)
  for id in definitionId do recordDef id
  let spanId ← required s.span "span"
  let preambleDefSpanId ← required s.preamble_def_span "preamble_def_span"
  recordSpan spanId
  recordSpan preambleDefSpanId
  validateLocalBounds locals.size blocks.size scopes.size
  return {
    mir := ⟨(← required s.phase "phase"), argumentCount, spreadArgument, locals.map (·.typeId), blocks.map (·.2.value)⟩,
    definitionId, defPath := s.def_path.join.getD sourcePath, sourcePath,
    spanId, preambleDefSpanId, injectionPhase := s.injection_phase.join,
    instanceId := (← required s.instance_id "instance_id"), localSources := locals.map (·.sourceInfo), sourceScopes := scopes,
    backtraceSpans, callEvidence := blocks.map (·.2.evidence), nodeFacts := blocks.map (·.2.facts),
    requiredConsts := (← required s.required_consts "required_consts"),
    promotedBodies := s.promoted_bodies.getD #[] }
def parseBodyRaw (sourcePath : String) : MIRParser.Parser Body := do
  finishParseBodyFields sourcePath (← MIRParser.object {} (parseBodyField sourcePath))

def parseSharedStatement (pools : MIRParser.SharedPools) : JsonReader.Parser MIRParser.SharedStatement := do
  let (value, state) ← statementKind.run {pools := some pools}
  pure ⟨value, state.references, state.facts, state.locals, state.blocks, state.scopes⟩

/-- Parse one constructor tree. Document decoding supplies schema pools;
standalone constructor tests may supply inline leaves without a document. -/
def parseBody (sourcePath : String) (pools : Option MIRParser.SharedPools := none) : JsonReader.Parser ParsedBody := do
  let (body, state) ← (parseBodyRaw sourcePath).run {pools}
  pure ⟨body, state.references⟩

end Miri.Input.DecodeMIR
