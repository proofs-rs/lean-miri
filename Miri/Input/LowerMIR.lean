import Miri.Input.Model
import Miri.Input.Decoder
import Miri.MIR.Syntax

/-! Fail-closed bridge from decoded compiler data to the fixed interpreter AST.
Successful lowering is syntax construction, not execution readiness or UB freedom.
The original envelope and source scopes remain available beside the MIR body. -/
namespace Miri.Input

abbrev LowerResult := Except String

structure LowerContext where
  /-- Each supplied type ID must refer to this compilation's metadata graph. -/
  spans : Array SourceSpanData := #[]
  layouts : Array Layout := #[]
  definitions : Array DefinitionId := #[]
  instances : Array InstanceNode := #[]
  typeConstants : Array MIR.TypeConst := #[]
  typeIds : Array TypeId
  /-- Exact byte widths from compiler layout metadata; required for scalar constants. -/
  scalarSizes : Array (TypeId × Nat)
  allocationIds : Array AllocationId := #[]
  obligations : Array Obligation := #[]
  /-- Paired source for query metadata addressed by paths in decoded MIR. -/
  sourceDocument : Option Lean.Json := none

/-- Consume complete import-time compiler values; manual contexts decode directly. -/
def LowerContext.decodeCompilerValue (ctx : LowerContext) (raw : Lean.Json) : Except String TypedValue :=
  DecoderValues.decodeCompilerValue raw

def LowerContext.decodeCompilerSpan (ctx : LowerContext) (raw : Lean.Json) : Except String TypedValue := do
  let id ← raw.getNat?
  unless id < ctx.spans.size do throw s!"missing source span {id}"
  pure (.sourceSpan id)

def LowerContext.containsTypeId (ctx : LowerContext) (id : TypeId) : Bool :=
  ctx.typeIds.contains id

def LowerContext.containsAllocationId (ctx : LowerContext) (id : AllocationId) : Bool :=
  ctx.allocationIds.contains id

def LowerContext.scalarSize (ctx : LowerContext) (id : TypeId) : Option Nat :=
  (ctx.scalarSizes.find? (fun pair => pair.1 == id)).map Prod.snd

def LowerContext.withTypeIds (ctx : LowerContext) (ids : Array TypeId) : LowerContext :=
  { ctx with typeIds := ids }

def LowerContext.withAllocationIds (ctx : LowerContext) (ids : Array AllocationId) : LowerContext :=
  { ctx with allocationIds := ids }

def LowerContext.withScalarSizes (ctx : LowerContext) (sizes : Array (TypeId × Nat)) : LowerContext :=
  { ctx with scalarSizes := sizes }

/-- Derive scalar widths from compiler metadata, never from bits or host types. -/
def LowerContext.ofTypes (types : Array TypeNode) (layouts : Array Layout := #[]) : LowerContext := Id.run do
  let typeIds := types.map (·.id)
  let scalarSizes := types.filterMap fun ty =>
    (layouts[ty.layoutId]?).bind fun layout => layout.sizeBytes.map (ty.id, ·)
  let obligations : Array Obligation := #[]
  let ctx : LowerContext := {
    typeIds
    scalarSizes
    allocationIds := #[]
    obligations
    sourceDocument := none
  }
  return ctx

/-- Resolve graph identities from the same decoded compilation. Metadata
semantics remain independent from syntax lowering and its obligations. -/
def LowerContext.ofDocument (document : ImportDocument) : LowerContext :=
  let ctx := (ofTypes document.types document.layouts).withAllocationIds (document.allocations.map (·.id))
  { ctx with
    sourceDocument := some document.raw
    spans := document.spans
    layouts := document.layouts
    definitions := document.definitions
    instances := document.instances
    typeConstants := document.typeConstants }

set_option autoImplicit false in
/-- A prepared lowering context tied to one exact decoded source document.
The private constructor and equality field prevent reusing it for a different
document, even when the documents serialize to equal JSON. -/
structure LowerContext.Bound (document : ImportDocument) where
  private mk ::
  value : LowerContext
  exact : value = LowerContext.ofDocument document

/-- Prepare the context and retain its exact document identity in the type. -/
def LowerContext.bindDocument (document : ImportDocument) : LowerContext.Bound document :=
  ⟨LowerContext.ofDocument document, rfl⟩

structure LoweredBody where
  body : MIR.Body
  spans : Array SourceSpanData
  input : BodyCore
  definitions : Array DefinitionId
  typeConstants : Array MIR.TypeConst
  obligations : Array Obligation

def lookupDefinitionId (definitions : Array DefinitionId) (id : Nat) : LowerResult MIR.DefId := do
  unless id < definitions.size do throw s!"unresolved compiler definition {id}"
  pure id

def LoweredBody.ownDefinitionId (body : LoweredBody) : LowerResult MIR.DefId := do
  let some id := body.input.definitionId | throw "body is missing its source definition identity"
  lookupDefinitionId body.definitions id

/-- Constructor inventory. `true` means a lowering branch exists, subject to
child metadata checks; it does not mean execution semantics is implemented.
Exhaustive matches make newly added input constructors require a decision. -/
def rvalueLoweringBranch : RvalueVariant → Bool
  | .use | .binaryOp | .unaryOp | .discriminant | .copyForDeref | .wrapUnsafeBinder => true
  | .repeat | .ref | .threadLocalRef | .rawPtr | .cast | .aggregate | .reborrow => true

def statementLoweringBranch : StatementVariant → Bool
  | .assign | .setDiscriminant | .storageLive | .storageDead | .placeMention | .constEvalCounter | .nop => true
  | .fakeRead | .ascribeUserType | .coverage | .intrinsic | .backwardIncompatibleDropHint => true

def terminatorLoweringBranch : TerminatorVariant → Bool
  | .goto | .unwindResume | .return | .unreachable | .assert | .coroutineDrop | .falseEdge => true
  | .switchInt | .unwindTerminate | .drop | .call | .tailCall | .yield | .falseUnwind | .inlineAsm => true

private abbrev Fields := Array (String × TypedValue)
private structure LowerState where
  spans : Array SourceSpanData := #[]
  definitions : Array DefinitionId := #[]
  typeConstants : Array MIR.TypeConst := #[]

private abbrev LowerM := StateT LowerState (Except String)

private def get (fs : Fields) (key : String) : LowerResult TypedValue :=
  match fs.find? (fun entry => entry.1 == key) with
  | some (_, v) => .ok v
  | none => .error s!"missing lowering field {key}"

private def fields : TypedValue → LowerResult Fields
  | .object fs | .enumTag _ _ fs => .ok fs
  | _ => .error "expected typed object"

private def nat : TypedValue → LowerResult Nat
  | .scalar j => j.getNat?
  | .localRef n | .blockRef n => .ok n
  | _ => .error "expected unsigned integer"

private def bool : TypedValue → LowerResult Bool
  | .scalar j => j.getBool?
  | _ => .error "expected boolean"

private def text : TypedValue → LowerResult String
  | .scalar j => j.getStr?
  | _ => .error "expected string"

private def array : TypedValue → LowerResult (Array TypedValue)
  | .array vs => .ok vs
  | _ => .error "expected typed array"

private def tag : TypedValue → LowerResult String
  | .enumTag _ t _ => .ok t.tag
  | .object fs => get fs "kind" >>= text
  | v => text v

private def typeId (ctx : LowerContext) : TypedValue → LowerResult MIR.TyId
  | .typeRef id => if ctx.containsTypeId id then .ok id else .error s!"unresolved type {id}"
  | _ => .error "expected type reference"

private def source (info : SourceInfo) : LowerM MIR.SourceInfo := do
  let state ← StateT.get
  unless info.spanId < state.spans.size do throw s!"missing source span {info.spanId}"
  return ⟨⟨info.spanId⟩, info.scope⟩

private def optional (lower : TypedValue → LowerResult α) : TypedValue → LowerResult (Option α)
  | .scalar .null => pure none
  | value => some <$> lower value

private def optionalM (lower : TypedValue → LowerM α) : TypedValue → LowerM (Option α)
  | .scalar .null => pure none
  | value => some <$> lower value

private def number (v : TypedValue) : LowerResult Nat := do
  match v with
  | .scalar (.str s) => match s.toNat? with | some n => pure n | none => throw "invalid decimal integer"
  | v => nat v

private def definition (v : TypedValue) : LowerM MIR.DefId := do
  let id ← nat v
  lookupDefinitionId (← StateT.get).definitions id

private def spanRef : TypedValue → LowerM MIR.SpanRef
  | .sourceSpan id => do
    unless id < (← StateT.get).spans.size do throw s!"missing source span {id}"
    pure ⟨id⟩
  | _ => throw "missing typed source span"

private def mutability (v : TypedValue) : LowerResult MIR.Mutability := do
  match ← tag v with
  | "mutable" => pure .Mut
  | "immutable" => pure .Not
  | _ => throw "unknown mutability"

private def safety (v : TypedValue) : LowerResult MIR.Safety := do
  match ← tag v with
  | "safe" => pure .Safe
  | "unsafe" => pure .Unsafe
  | _ => throw "unknown safety"

private def castKind (v : TypedValue) : LowerResult MIR.CastKind := do
  let fs ← fields v
  match ← tag v with
  | "PointerExposeProvenance" => pure .PointerExposeProvenance
  | "PointerWithExposedProvenance" => pure .PointerWithExposedProvenance
  | "PointerCoercion" =>
    let c ← get fs "coercion"
    let cf ← fields c
    let coercion ← (show LowerResult MIR.PointerCoercion from match ← tag c with
      | "ReifyFnPointer" => return MIR.PointerCoercion.ReifyFnPointer (← safety (← get cf "safety"))
      | "UnsafeFnPointer" => pure .UnsafeFnPointer
      | "ClosureFnPointer" => return .ClosureFnPointer (← safety (← get cf "safety"))
      | "MutToConstPointer" => pure .MutToConstPointer
      | "ArrayToPointer" => pure .ArrayToPointer
      | "Unsize" => pure .Unsize
      | _ => throw "unknown pointer coercion")
    let source ← match ← tag (← get fs "source") with
      | "as_cast" => pure MIR.CoercionSource.AsCast
      | "implicit" => pure .Implicit
      | _ => throw "unknown coercion source"
    pure (.PointerCoercion coercion source)
  | "IntToInt" => pure .IntToInt
  | "FloatToInt" => pure .FloatToInt
  | "FloatToFloat" => pure .FloatToFloat
  | "IntToFloat" => pure .IntToFloat
  | "PtrToPtr" => pure .PtrToPtr
  | "FnPtrToPtr" => pure .FnPtrToPtr
  | "Transmute" => pure .Transmute
  | "BoxDerefTransmute" => pure .BoxDerefTransmute
  | "Subtype" => pure .Subtype
  | _ => throw "unknown cast kind"

private def boundIndex (v : TypedValue) : LowerResult MIR.BoundVarIndexKind := do
  let fs ← fields v
  match ← tag v with
  | "bound" => return .Bound (← nat (← get fs "debruijn_index"))
  | "canonical" => pure .Canonical
  | _ => throw "unknown bound index kind"

private def boundRegion (v : TypedValue) : LowerM MIR.BoundRegionKind := do
  let fs ← fields v
  match ← tag v with
  | "anonymous" => pure .Anon
  | "named_for_printing" => return .NamedForPrinting (← text (← get fs "name"))
  | "named" => return .Named (← definition (← get fs "def_id"))
  | "closure_environment" => pure .ClosureEnv
  | _ => throw "unknown bound region kind"

private def region (v : TypedValue) : LowerM MIR.Region := do
  let fs ← fields v
  match ← tag v with
  | "early_parameter" => return .EarlyParameter (← nat (← get fs "index")) (← text (← get fs "name"))
  | "bound" => return .Bound (← boundIndex (← get fs "index_kind")) (← nat (← get fs "variable_index")) (← boundRegion (← get fs "bound_kind"))
  | "late_parameter" =>
    let p ← get fs "parameter"
    let pf ← fields p
    let kind ← (show LowerM MIR.LateParamRegionKind from match ← tag p with
      | "anonymous" => return .Anon (← nat (← get pf "index"))
      | "named_anonymous" => return .NamedAnon (← nat (← get pf "index")) (← text (← get pf "name"))
      | "named" => return .Named (← definition (← get pf "def_id"))
      | "closure_environment" => pure .ClosureEnv
      | _ => throw "unknown late parameter region")
    return .LateParameter (← definition (← get fs "scope_def_id")) kind
  | "static" => pure .Static
  | "placeholder" => return .Placeholder (← nat (← get fs "universe")) (← nat (← get fs "variable_index")) (← boundRegion (← get fs "bound_kind"))
  | "erased" => pure .Erased
  | _ => throw "unknown region"

private def borrow (v : TypedValue) : LowerResult MIR.BorrowKind := do
  let fs ← fields v
  match ← tag v with
  | "shared" => pure .Shared
  | "fake" =>
    match ← tag (← get fs "fake_kind") with
    | "shallow" => pure (.Fake .Shallow)
    | "deep" => pure (.Fake .Deep)
    | _ => throw "unknown fake borrow"
  | "mutable" =>
    match ← tag (← get fs "mutability_kind") with
    | "default" => pure (.Mut .Default)
    | "two_phase" => pure (.Mut .TwoPhaseBorrow)
    | "closure_capture" => pure (.Mut .ClosureCapture)
    | _ => throw "unknown mutable borrow"
  | _ => throw "unknown borrow kind"

private def projection (ctx : LowerContext) : TypedValue → LowerResult MIR.ProjectionElem
  | .projection k fs => do
    match k with
    | .deref => pure .Deref
    | .field => return .Field (← nat (← get fs "index")) (← typeId ctx (← get fs "field_type"))
    | .index => return .Index (← nat (← get fs "local"))
    | .constantIndex => return .ConstantIndex (← nat (← get fs "offset")) (← nat (← get fs "min_length")) (← bool (← get fs "from_end"))
    | .subslice => return .Subslice (← nat (← get fs "from")) (← nat (← get fs "to")) (← bool (← get fs "from_end"))
    | .downcast =>
      let name ← match ← get fs "name" with
        | .scalar .null => pure none
        | v => some <$> text v
      return .Downcast name (← nat (← get fs "variant_index"))
    | .opaqueCast => return .OpaqueCast (← typeId ctx (← get fs "cast_type"))
    | .unwrapUnsafeBinder => return .UnwrapUnsafeBinder (← typeId ctx (← get fs "inner_type"))
    | .phantomDeref => pure .PhantomDeref
  | _ => .error "expected projection"

private def place (ctx : LowerContext) (v : TypedValue) : LowerResult MIR.Place := do
  let fs ← fields v
  return ⟨← nat (← get fs "local"), ← (← array (← get fs "projection")).mapM (projection ctx)⟩

private def binOp (v : TypedValue) : LowerResult MIR.BinOp := do
  match v with
  | .binOperator op => pure op
  | _ =>
    match ← tag v with
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

private def unOp (v : TypedValue) : LowerResult MIR.UnOp := do
  match v with
  | .unOperator op => pure op
  | _ =>
    match ← tag v with
    | "not" => pure .Not
    | "negate" => pure .Neg
    | "pointer_metadata" => pure .PtrMetadata
    | _ => throw "unknown unary operator"

private def typeConstRef (ctx : LowerContext) (value : TypedValue) : LowerResult MIR.TypeConstId := do
  let id ← nat value
  unless id < ctx.typeConstants.size do throw s!"unresolved type constant {id}"
  pure id

private def genericArgs (ctx : LowerContext) (v : TypedValue) : LowerM (Array MIR.GenericArg) := do
  (← array v).mapM fun arg => do
    let fs ← fields arg
    match ← tag arg with
    | "type" => return .Type (← typeId ctx (← get fs "value"))
    | "lifetime" => return .Lifetime (← region (← get fs "value"))
    | "const" => return .Const (← typeConstRef ctx (← get fs "value"))
    | _ => throw "unknown generic argument"

private def initialState (ctx : LowerContext) : LowerResult LowerState :=
  pure { spans := ctx.spans, definitions := ctx.definitions, typeConstants := ctx.typeConstants }

private def annotation (v : TypedValue) : LowerResult Nat := do
  match v with
  | .scalar (.num _) => nat v
  | _ => let fs ← fields v; nat (← get fs "index")

private def aggregate (ctx : LowerContext) (v : TypedValue) : LowerM MIR.AggregateKind := do
  let fs ← fields v
  match ← tag v with
  | "Array" => return .Array (← typeId ctx (← get fs "element_type"))
  | "Tuple" => pure .Tuple
  | "Adt" =>
    return .Adt (← definition (← get fs "def_id")) (← nat (← get fs "variant_index"))
      (← genericArgs ctx (← get fs "generic_args")) (← optional annotation (← get fs "user_type_annotation"))
      (← optional nat (← get fs "active_union_field"))
  | "Closure" => return .Closure (← definition (← get fs "def_id")) (← genericArgs ctx (← get fs "generic_args"))
  | "Coroutine" => return .Coroutine (← definition (← get fs "def_id")) (← genericArgs ctx (← get fs "generic_args"))
  | "CoroutineClosure" => return .CoroutineClosure (← definition (← get fs "def_id")) (← genericArgs ctx (← get fs "generic_args"))
  | "RawPtr" => return .RawPtr (← typeId ctx (← get fs "pointee_type")) (← mutability (← get fs "mutability"))
  | _ => throw "unknown aggregate kind"

private def allocationId (ctx : LowerContext) : TypedValue → LowerResult MIR.AllocationId
  | .allocationRef id => if ctx.containsAllocationId id then pure id else throw s!"unresolved allocation {id}"
  | _ => throw "unresolved allocation reference"

private def constValue (ctx : LowerContext) (ty : MIR.TyId) (v : TypedValue) : LowerResult MIR.ConstValue := do
  let fs ← fields v
  match ← tag v with
  | "zero_sized" => pure .ZeroSized
  | "scalar" =>
    let bits ← number (← get fs "bits_unsigned")
    let size ← match ctx.scalarSize ty with
      | some size => pure size
      | none => throw s!"missing scalar byte width for type {ty}"
    unless size > 0 && bits < 2 ^ (8 * size) do throw "scalar bits exceed byte width"
    pure (.Scalar (.Int bits size))
  | "pointer_scalar" => return .Scalar (.Ptr (.Allocation (← allocationId ctx (← get fs "allocation")) (← nat (← get fs "offset_bytes")) (← bool (← get fs "immutable")) (← bool (← get fs "shared_ref"))))
  | "pointer_scalar_without_provenance" => return .Scalar (.Ptr (.Address (← number (← get fs "address")) (← nat (← get fs "address_width_bytes"))))
  | "slice_allocation" => return .Slice (← allocationId ctx (← get fs "allocation")) (← nat (← get fs "metadata_length"))
  | "indirect_allocation" => return .Indirect (← allocationId ctx (← get fs "allocation")) (← nat (← get fs "offset_bytes"))
  | _ => throw "unknown or unavailable evaluated constant"

private def constOperand (ctx : LowerContext) (v : TypedValue) : LowerM MIR.ConstOperand := do
  let c ← fields v
  let ty ← typeId ctx (← get c "type")
  let userType ← optional annotation (← get c "user_type_annotation")
  let span ← spanRef (← get c "span")
  let evaluated ← fields (← get c "constant")
  let originalValue ← get evaluated "source"
  let original ← fields originalValue
  let constant ← (show LowerM MIR.MirConst from match ← tag originalValue with
    | "already_evaluated" => return .Val (← constValue ctx ty (← get evaluated "value")) ty
    | "type_system_const" => return .Ty (← typeId ctx (← get original "type")) (← typeConstRef ctx (← get original "const"))
    | "unevaluated" => return .Unevaluated ⟨← definition (← get original "def_id"), ← genericArgs ctx (← get original "generic_args"), ← optional nat (← get original "promoted")⟩ (← typeId ctx (← get original "type"))
    | _ => throw "unknown MIR constant source")
  pure ⟨span, userType, constant⟩

private def operand (ctx : LowerContext) : TypedValue → LowerM MIR.Operand
  | .operand k fs => do
    match k with
    | .copy => return .Copy (← place ctx (← get fs "place"))
    | .move => return .Move (← place ctx (← get fs "place"))
    | .runtimeChecks =>
      let check ← tag (← get fs "check")
      let check ← match check with
        | "ub_checks" => pure MIR.RuntimeChecks.UbChecks
        | "contract_checks" => pure .ContractChecks
        | "overflow_checks" => pure .OverflowChecks
        | _ => throw "unknown runtime check"
      return .RuntimeChecks check
    | .constant => return .Constant (← constOperand ctx (← get fs "constant"))
  | _ => throw "unsupported or malformed operand"

private def rvalue (ctx : LowerContext) : TypedValue → LowerM MIR.Rvalue
  | .rvalue k fs => do
    match k with
    | .use =>
      let retag ← tag (← get fs "retag")
      let retag ← match retag with
        | "yes" => pure MIR.WithRetag.Yes
        | "no" => pure .No
        | _ => throw "unknown retag mode"
      return .Use (← operand ctx (← get fs "operand")) retag
    | .binaryOp =>
      let op ← match ← get fs "operator" with
        | .binOperator op => pure op
        | _ => throw "unsupported binary operator"
      return .BinaryOp op (← operand ctx (← get fs "left")) (← operand ctx (← get fs "right"))
    | .unaryOp =>
      let op ← match ← get fs "operator" with
        | .unOperator op => pure op
        | _ => throw "unsupported unary operator"
      return .UnaryOp op (← operand ctx (← get fs "operand"))
    | .discriminant => return .Discriminant (← place ctx (← get fs "place"))
    | .copyForDeref => return .CopyForDeref (← place ctx (← get fs "place"))
    | .wrapUnsafeBinder => return .WrapUnsafeBinder (← operand ctx (← get fs "operand")) (← typeId ctx (← get fs "type"))
    | .repeat => return .Repeat (← operand ctx (← get fs "operand")) (← typeConstRef ctx (← get fs "count"))
    | .ref => return .Ref (← region (← get fs "region")) (← borrow (← get fs "borrow_kind")) (← place ctx (← get fs "place"))
    | .threadLocalRef => return .ThreadLocalRef (← definition (← get fs "def_id"))
    | .rawPtr =>
      let kind ← (show LowerM MIR.RawPtrKind from match ← tag (← get fs "pointer_kind") with
        | "mutable" => pure .Mut
        | "constant" => pure .Const
        | "metadata_only" => pure .FakeForPtrMetadata
        | _ => throw "unknown raw pointer kind")
      return .RawPtr kind (← place ctx (← get fs "place"))
    | .cast => return .Cast (← castKind (← get fs "cast_kind")) (← operand ctx (← get fs "operand")) (← typeId ctx (← get fs "target_type"))
    | .aggregate => return .Aggregate (← aggregate ctx (← get fs "aggregate_kind")) (← (← array (← get fs "operands")).mapM (operand ctx))
    | .reborrow => return .Reborrow (← typeId ctx (← get fs "type")) (← mutability (← get fs "mutability")) (← place ctx (← get fs "place"))
  | _ => throw "unsupported or malformed rvalue"

private def fakeRead (v : TypedValue) : LowerM MIR.FakeReadCause := do
  let fs ← fields v
  match ← tag v with
  | "match_guard" => pure .ForMatchGuard
  | "matched_place" => return .ForMatchedPlace (← optionalM definition (← get fs "hoisted_from"))
  | "guard_binding" => pure .ForGuardBinding
  | "let_binding" => return .ForLet (← optionalM definition (← get fs "hoisted_from"))
  | "index" => pure .ForIndex
  | _ => throw "unknown fake read cause"

private def variance (v : TypedValue) : LowerResult MIR.Variance := do
  match ← tag v with
  | "covariant" => pure .Covariant
  | "contravariant" => pure .Contravariant
  | "invariant" => pure .Invariant
  | "bivariant" => pure .Bivariant
  | _ => throw "unknown variance"

private def userProjectionKind : UserTypeProjectionKind → LowerResult MIR.ProjectionKind
  | .deref => pure .Deref
  | .field i => pure (.Field i)
  | .index => pure .Index
  | .constantIndex a b c => pure (.ConstantIndex a b c)
  | .subslice a b c => pure (.Subslice a b c)
  | .downcast a b => pure (.Downcast a b)
  | .opaqueCast => pure .OpaqueCast
  | .unwrapUnsafeBinder => pure .UnwrapUnsafeBinder
  | .phantomDeref => pure .PhantomDeref

private def userProjection : TypedValue → LowerResult MIR.UserTypeProjection
  | .userTypeProjection p => do
    let some base := p.baseIndex | throw "missing user projection base"
    let some ps := p.projections | throw "missing user projections"
    return ⟨base, ← ps.mapM userProjectionKind⟩
  | _ => throw "missing typed user projection"

private def coverage (v : TypedValue) : LowerM MIR.CoverageKind := do
  let fs ← fields v
  match ← tag v with
  | "point" =>
    let kind ← (show LowerM MIR.CoveragePointKind from match ← tag (← get fs "point_kind") with
      | "expr" => pure .Expr
      | "implicit_else" => pure .ImplicitElse
      | "function_end" => pure .FunctionEnd
      | _ => throw "unknown coverage point")
    let hir ← fields (← get fs "hir_id")
    return .Point kind ⟨← definition (← get hir "owner_def_id"), ← nat (← get hir "local_id")⟩
  | "block_marker" => return .BlockMarker (← nat (← get fs "id"))
  | "virtual_counter" => return .VirtualCounter (← nat (← get fs "bcb"))
  | _ => throw "unknown coverage kind"

private def statement (ctx : LowerContext) (node : MirNode) : LowerM MIR.Statement := do
  let kind ← (show LowerM MIR.StatementKind from match node.value with
    | .statement k fs => do
      match k with
      | .assign => return MIR.StatementKind.Assign (← place ctx (← get fs "place")) (← rvalue ctx (← get fs "rvalue"))
      | .storageLive => return .StorageLive (← nat (← get fs "local"))
      | .storageDead => return .StorageDead (← nat (← get fs "local"))
      | .placeMention => return .PlaceMention (← place ctx (← get fs "place"))
      | .setDiscriminant => return .SetDiscriminant (← place ctx (← get fs "place")) (← nat (← get fs "variant_index"))
      | .constEvalCounter => pure .ConstEvalCounter
      | .nop => pure .Nop
      | .fakeRead => return .FakeRead (← fakeRead (← get fs "cause")) (← place ctx (← get fs "place"))
      | .ascribeUserType => return .AscribeUserType (← place ctx (← get fs "place")) (← userProjection (← get fs "user_type_projection")) (← variance (← get fs "variance"))
      | .coverage => return .Coverage (← coverage (← get fs "coverage"))
      | .intrinsic =>
        let intrinsic ← (show LowerM MIR.NonDivergingIntrinsic from match ← text (← get fs "intrinsic") with
          | "Assume" => return .Assume (← operand ctx (← get fs "value"))
          | "CopyNonOverlapping" => return .CopyNonOverlapping ⟨← operand ctx (← get fs "src"), ← operand ctx (← get fs "dst"), ← operand ctx (← get fs "count")⟩
          | _ => throw "unknown nondiverging intrinsic")
        pure (.Intrinsic intrinsic)
      | .backwardIncompatibleDropHint =>
        unless (← tag (← get fs "reason")) == "edition_2024" do throw "unknown backward drop reason"
        return .BackwardIncompatibleDropHint (← place ctx (← get fs "place")) .Edition2024
    | _ => throw "unsupported or malformed statement")
  return ⟨← source node.sourceInfo, kind⟩

private def unwindReason (v : TypedValue) : LowerResult MIR.UnwindTerminateReason := do
  match ← tag v with
  | "abi" => pure .Abi
  | "in_cleanup" => pure .InCleanup
  | _ => throw "unknown unwind termination reason"

private def coroutine (v : TypedValue) : LowerResult MIR.CoroutineKind := do
  let fs ← fields v
  match ← tag v with
  | "desugared" =>
    let desugaring ← (show LowerResult MIR.CoroutineDesugaring from match ← text (← get fs "desugaring") with
      | "async" => pure .Async
      | "gen" => pure .Gen
      | "async_gen" => pure .AsyncGen
      | _ => throw "unknown coroutine desugaring")
    let source ← (show LowerResult MIR.CoroutineSource from match ← text (← get fs "source") with
      | "block" => pure .Block
      | "closure" => pure .Closure
      | "function" => pure .Fn
      | _ => throw "unknown coroutine source")
    pure (.Desugared desugaring source)
  | "coroutine" =>
    match ← text (← get fs "movability") with
    | "static" => pure (.Coroutine .Static)
    | "movable" => pure (.Coroutine .Movable)
    | _ => throw "unknown coroutine movability"
  | _ => throw "unknown coroutine kind"

private def unwind (v : TypedValue) : LowerResult MIR.UnwindAction := do
  let fs ← fields v
  match ← text (← get fs "kind") with
  | "Continue" => pure .Continue
  | "Unreachable" => pure .Unreachable
  | "Cleanup" => return .Cleanup (← nat (← get fs "target"))
  | "Terminate" => return .Terminate (← unwindReason (← get fs "reason"))
  | _ => throw "unknown unwind action"

private def assertKind (ctx : LowerContext) (v : TypedValue) : LowerM MIR.AssertKind := do
  let fs ← fields v
  match ← tag v with
  | "Overflow" =>
    let op ← match ← get fs "operator" with
      | .binOperator op => pure op
      | _ => throw "unsupported assertion operator"
    return .Overflow op (← operand ctx (← get fs "left")) (← operand ctx (← get fs "right"))
  | "BoundsCheck" => return .BoundsCheck (← operand ctx (← get fs "length")) (← operand ctx (← get fs "index"))
  | "OverflowNeg" => return .OverflowNeg (← operand ctx (← get fs "operand"))
  | "DivisionByZero" => return .DivisionByZero (← operand ctx (← get fs "operand"))
  | "RemainderByZero" => return .RemainderByZero (← operand ctx (← get fs "operand"))
  | "NullPointerDereference" => pure .NullPointerDereference
  | "NullReferenceConstructed" => pure .NullReferenceConstructed
  | "ResumedAfterReturn" => return .ResumedAfterReturn (← coroutine (← get fs "coroutine_kind"))
  | "ResumedAfterPanic" => return .ResumedAfterPanic (← coroutine (← get fs "coroutine_kind"))
  | "ResumedAfterDrop" => return .ResumedAfterDrop (← coroutine (← get fs "coroutine_kind"))
  | "MisalignedPointerDereference" => return .MisalignedPointerDereference (← operand ctx (← get fs "required")) (← operand ctx (← get fs "found"))
  | "InvalidEnumConstruction" => return .InvalidEnumConstruction (← operand ctx (← get fs "operand"))
  | _ => throw "unknown assertion kind"

private def loopHint (v : TypedValue) : LowerResult MIR.LoopHintAttr := do
  let fs ← fields v
  match ← text (← get fs "kind") with
  | "Hint" => pure .Hint
  | "Full" => pure .Full
  | "Never" => pure .Never
  | "Count" => return .Count (← nat (← get fs "count"))
  | _ => throw "unknown loop hint"

private def callSource (v : TypedValue) : LowerResult MIR.CallSource := do
  match ← tag v with
  | "overloaded_operator" => pure .OverloadedOperator
  | "match_comparison" => pure .MatchCmp
  | "miscellaneous_desugaring" => pure .Misc
  | "clone_or_use" => pure .Use
  | "normal_call" => pure .Normal
  | _ => throw "unknown call source"

private def spannedOperand (ctx : LowerContext) (v : TypedValue) : LowerM MIR.SpannedOperand := do
  let fs ← fields v
  return ⟨← spanRef (← get fs "span"), ← operand ctx (← get fs "operand")⟩

private def asmArch (v : TypedValue) : LowerResult MIR.InlineAsmArch := do
  match ← text v with
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
  | _ => throw "unknown assembly architecture"

private def asmRegister (v : TypedValue) : LowerResult MIR.InlineAsmRegOrRegClass := do
  let fs ← fields v
  let arch ← asmArch (← get fs "arch")
  let name ← text (← get fs "name")
  match ← tag v with
  | "register" => pure (.Reg arch name)
  | "register_class" => pure (.RegClass arch name)
  | _ => throw "unknown assembly register kind"

private def asmPiece (v : TypedValue) : LowerM MIR.InlineAsmTemplatePiece := do
  let fs ← fields v
  match ← tag v with
  | "string" => return .String (← text (← get fs "text"))
  | "placeholder" =>
    let modifier ← optional (fun value => do
      let s ← text value
      match s.toList with
      | [c] => pure c
      | _ => throw "assembly modifier must be one character") (← get fs "modifier")
    return .Placeholder (← nat (← get fs "operand_index")) modifier (← spanRef (← get fs "span"))
  | _ => throw "unknown assembly template piece"

private def asmOperand (ctx : LowerContext) (v : TypedValue) : LowerM MIR.InlineAsmOperand := do
  let fs ← fields v
  match ← tag v with
  | "in" => return .In (← asmRegister (← get fs "register")) (← operand ctx (← get fs "value"))
  | "out" => return .Out (← asmRegister (← get fs "register")) (← bool (← get fs "late")) (← optional (place ctx) (← get fs "place"))
  | "inout" => return .InOut (← asmRegister (← get fs "register")) (← bool (← get fs "late")) (← operand ctx (← get fs "input")) (← optional (place ctx) (← get fs "output"))
  | "const" => return .Const (← constOperand ctx (← get fs "value"))
  | "sym_fn" => return .SymFn (← constOperand ctx (← get fs "value"))
  | "sym_static" => return .SymStatic (← definition (← get fs "def_id"))
  | "label" => return .Label (← nat (← get fs "target_index"))
  | _ => throw "unknown assembly operand"

private def inlineAsm (ctx : LowerContext) (fs : Fields) : LowerM MIR.InlineAsmTerminator := do
  let macroKind ← (show LowerM MIR.InlineAsmMacro from match ← text (← get fs "asm_macro") with
    | "asm" => pure .Asm
    | "naked_asm" => pure .NakedAsm
    | _ => throw "unknown assembly macro")
  let options ← fields (← get fs "options")
  let options : MIR.InlineAsmOptions := ⟨← bool (← get options "pure"), ← bool (← get options "nomem"),
    ← bool (← get options "readonly"), ← bool (← get options "preserves_flags"), ← bool (← get options "noreturn"),
    ← bool (← get options "nostack"), ← bool (← get options "att_syntax"), ← bool (← get options "raw"), ← bool (← get options "may_unwind")⟩
  let template ← (← array (← get fs "template")).mapM asmPiece
  let operands ← (← array (← get fs "operands")).mapM (asmOperand ctx)
  let spans ← (← array (← get fs "line_spans")).mapM spanRef
  let targets ← ((← array (← get fs "targets")).mapM nat : LowerResult _)
  for op in operands do
    match op with
    | .Label index => unless index < targets.size do throw "assembly label index exceeds target list"
    | _ => pure ()
  for piece in template do
    match piece with
    | .Placeholder index _ _ => unless index < operands.size do throw "assembly placeholder exceeds operand list"
    | _ => pure ()
  return ⟨macroKind, template, operands, options, spans, targets, ← unwind (← get fs "unwind")⟩

private def terminator (ctx : LowerContext) (node : MirNode) : LowerM MIR.Terminator := do
  let kind ← (show LowerM MIR.TerminatorKind from match node.value with
    | .terminator k fs => do
      match k with
      | .return => pure MIR.TerminatorKind.Return
      | .unreachable => pure .Unreachable
      | .unwindResume => pure .UnwindResume
      | .coroutineDrop => pure .CoroutineDrop
      | .assert => return .Assert (← operand ctx (← get fs "condition")) (← bool (← get fs "expected")) (← assertKind ctx (← get fs "message")) (← nat (← get fs "target")) (← unwind (← get fs "unwind"))
      | .falseEdge => return .FalseEdge (← nat (← get fs "real_target")) (← nat (← get fs "imaginary_target"))
      | .goto =>
        let hints ← array (← get fs "loop_hints")
        let lowered ← (hints.mapM loopHint : LowerResult _ )
        return .Goto (← nat (← get fs "target")) lowered
      | .switchInt =>
        let cases ← (← array (← get fs "targets")).mapM fun entry => do
          let ef ← fields entry
          pure (MIR.SwitchTarget.Case (← number (← get ef "value")) (← nat (← get ef "target")))
        return .SwitchInt (← operand ctx (← get fs "discriminant")) ⟨cases, ← nat (← get fs "otherwise")⟩
      | .unwindTerminate => return .UnwindTerminate (← unwindReason (← get fs "reason"))
      | .drop => return .Drop (← place ctx (← get fs "place")) (← nat (← get fs "target")) (← unwind (← get fs "unwind")) (← bool (← get fs "replace")) (← optional nat (← get fs "async_drop"))
      | .call => return .Call (← operand ctx (← get fs "function")) (← (← array (← get fs "args")).mapM (spannedOperand ctx)) (← place ctx (← get fs "destination")) (← optional nat (← get fs "target")) (← unwind (← get fs "unwind")) (← callSource (← get fs "call_source")) (← spanRef (← get fs "function_span"))
      | .tailCall => return .TailCall (← operand ctx (← get fs "function")) (← (← array (← get fs "args")).mapM (spannedOperand ctx)) (← spanRef (← get fs "function_span"))
      | .yield => return .Yield (← operand ctx (← get fs "value")) (← nat (← get fs "resume")) (← place ctx (← get fs "resume_arg")) (← optional nat (← get fs "drop"))
      | .falseUnwind => return .FalseUnwind (← nat (← get fs "real_target")) (← unwind (← get fs "unwind"))
      | .inlineAsm => return .InlineAsm (← inlineAsm ctx fs)
    | _ => throw "unsupported or malformed terminator")
  return ⟨← source node.sourceInfo, kind⟩

private def phase : TypedValue → LowerResult MIR.MirPhase
  | .enumTag .mirPhase t fs => do
    match t.tag with
    | "built" => pure .Built
    | "analysis" =>
      match ← tag (← get fs "phase") with
      | "initial" => pure (.Analysis .Initial)
      | "post_cleanup" => pure (.Analysis .PostCleanup)
      | _ => throw "unknown analysis phase"
    | "runtime" =>
      match ← tag (← get fs "phase") with
      | "initial" => pure (.Runtime .Initial)
      | "post_cleanup" => pure (.Runtime .PostCleanup)
      | "optimized" => pure (.Runtime .Optimized)
      | _ => throw "unknown runtime phase"
    | _ => throw "unknown MIR phase"
  | _ => .error "missing typed MIR phase"

private partial def validateReferences (ctx : LowerContext) (locals blocks : Nat)
    (v : TypedValue) : LowerResult Unit := do
  match v with
  | .typeRef id => unless ctx.containsTypeId id do throw s!"unresolved type {id}"
  | .allocationRef id => unless ctx.containsAllocationId id do throw s!"unresolved allocation {id}"
  | .localRef id => unless id < locals do throw s!"out-of-range local {id}"
  | .blockRef id => unless id < blocks do throw s!"out-of-range block {id}"
  | .array vs => for child in vs do validateReferences ctx locals blocks child
  | .object fs | .statement _ fs | .terminator _ fs | .rvalue _ fs
  | .operand _ fs | .projection _ fs | .enumTag _ _ fs =>
    for (_, child) in fs do validateReferences ctx locals blocks child
  | .diagnostic _ => pure ()
  | _ => pure ()

private partial def payloadObligations (sourceDocument : Option Lean.Json)
    (v : TypedValue) (path : String) : Array Obligation := Id.run do
  match v with
  | .array vs => return (vs.toList.zipIdx).foldl (fun out (child, i) => out ++ payloadObligations sourceDocument child s!"{path}[{i}]") #[]
  | .diagnostic _ => return #[⟨path, "diagnostic-only compiler metadata remains unresolved"⟩]
  | _ => pure ()
  let (own, children) : Array Obligation × Fields := match v with
    | .statement _ fs | .terminator _ fs | .rvalue _ fs | .operand _ fs => (#[], fs)
    | .enumTag _ _ fs => (#[], fs)
    | .object fs | .projection _ fs => (#[], fs)
    | _ => (#[], #[])
  let mut out := own
  for (key, child) in children do
    out := out ++ payloadObligations sourceDocument child (path ++ "." ++ key)
  return out

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

/-- Unsupported constructors and missing metadata remain errors. -/
private def lowerBodyState (ctx : LowerContext) (input : BodyCore) (initial : LowerState) : LowerResult (LoweredBody × LowerState) := do
  let mirPhase ← phase input.phase
  match input.injectionPhase with
  | some value => let _ ← phase value; pure ()
  | none => pure ()
  unless !input.blocks.isEmpty do throw "body has no entry basic block"
  let scopes ← match input.sourceScopes with
    | some scopes => pure scopes
    | none => throw "missing source scope metadata"
  for decl in input.locals do
    unless decl.sourceInfo.scope < scopes.size do throw "unresolved local source scope"
  unless input.argumentCount < input.locals.size do throw "argument count exceeds locals"
  for (decl, i) in input.locals.toList.zipIdx do
    unless decl.id == i do throw "noncontiguous local IDs"
    unless ctx.containsTypeId decl.typeId do throw s!"unresolved local type {decl.typeId}"
  for (block, i) in input.blocks.toList.zipIdx do
    unless block.id == i do throw "noncontiguous basic block IDs"
    for node in block.statements.push block.terminator do
      unless node.sourceInfo.scope < scopes.size do throw "unresolved instruction source scope"
      validateReferences ctx input.locals.size input.blocks.size node.value
  match input.spreadArgument with
  | some arg => unless arg > 0 && arg ≤ input.argumentCount do throw "invalid spread argument"
  | none => pure ()
  let action : LowerM (Array MIR.BasicBlock) := input.blocks.mapM fun block => do
    return ⟨← block.statements.mapM (statement ctx), ← terminator ctx block.terminator, block.cleanup⟩
  if let some id := input.definitionId then
    let _ ← lookupDefinitionId initial.definitions id
  let (blocks, state) ← action.run initial
  for block in blocks do
    for target in controlTargets block.terminator.kind do
      unless target < blocks.size do throw s!"out-of-range control-flow target {target}"
  let obligations := input.blocks.toList.zipIdx.foldl (fun out (block, blockIndex) => Id.run do
    let bodyPrefix := if input.sourcePath.isEmpty then "" else input.sourcePath ++ "."
    let blockPrefix := s!"{bodyPrefix}basic_blocks[{blockIndex}]"
    let statements := block.statements.toList.zipIdx.foldl (fun issues (node, statementIndex) =>
      issues ++ payloadObligations ctx.sourceDocument node.value
        s!"{blockPrefix}.statements[{statementIndex}].kind") #[]
    let terminator := payloadObligations ctx.sourceDocument block.terminator.value
      s!"{blockPrefix}.terminator.kind"
    return out ++ statements ++ terminator) ctx.obligations
  let obligations := if input.definitionId.isSome then obligations else
    obligations.push ⟨"body.definitionId", "source definition identity is missing; runtime frame initialization must fail until supplied"⟩
  return (⟨⟨mirPhase, input.argumentCount, input.spreadArgument, input.locals.map (·.typeId), blocks⟩, state.spans, input, state.definitions, state.typeConstants, obligations⟩, state)

/-- A standalone body's definition/type-constant/span IDs are local to this
result. Use `lowerBodies` or `lowerProgram` for cross-function linking. -/
def lowerBody (ctx : LowerContext) (input : BodyCore) : LowerResult LoweredBody := do
  (lowerBodyState ctx input (← initialState ctx)).map Prod.fst

structure LoweredBodies where
  bodies : Array LoweredBody
  spans : Array SourceSpanData
  definitions : Array DefinitionId
  typeConstants : Array MIR.TypeConst


def lowerBodies (ctx : LowerContext) (inputs : Array BodyCore) : LowerResult LoweredBodies := do
  let mut state ← initialState ctx
  let mut bodies := #[]
  for input in inputs do
    let (body, next) ← lowerBodyState ctx input state
    bodies := bodies.push body
    state := next
  bodies := bodies.map fun body =>
    { body with
      spans := state.spans
      definitions := state.definitions
      typeConstants := state.typeConstants }
  pure ⟨bodies, state.spans, state.definitions, state.typeConstants⟩

structure LoweredProgram where
  bundle : LoweredBodies
  /-- Root body indices into `bundle.bodies`, in the original document order. -/
  roots : Array Nat
  /-- Instance graph identity to body index; the source graph is retained below. -/
  instances : Array (InstanceId × Nat)
  /-- (parent body index, promoted index, body index). -/
  promoted : Array (Nat × Nat × Nat)
  input : ImportDocument

/-- Normalization rows supply compiler evidence without becoming execution roots. -/
def LoweredProgram.executableBodyIds (program : LoweredProgram) : Array Nat := Id.run do
  let mut pending := program.roots ++ program.instances.map Prod.snd
  let mut seen : Std.HashSet Nat := {}
  while !pending.isEmpty do
    let current := pending
    pending := #[]
    for id in current do
      if seen.contains id then continue
      seen := seen.insert id
      for (parent, _, child) in program.promoted do
        if parent == id then pending := pending.push child
  return (Array.range program.bundle.bodies.size).filter seen.contains

/-- Look up a document root's frame identity without assuming it was called
or that source and runtime definition indices coincide. -/
def LoweredProgram.rootDefinitionId (program : LoweredProgram) (rootIndex : Nat)
    : LowerResult MIR.DefId := do
  let some bodyIndex := program.roots[rootIndex]? | throw "root index is out of range"
  let some body := program.bundle.bodies[bodyIndex]? | throw "root body index is out of range"
  body.ownDefinitionId

/-- Lower all present root, instance, and promoted bodies with global compiler
identity tables. Unavailable bodies remain explicit source graph obligations. -/
def lowerProgram (input : ImportDocument) : LowerResult LoweredProgram := do
  let mut roots := #[]
  let mut instances := #[]
  let mut promoted := #[]
  for root in input.bodyRoots do
    unless root.bodyId < input.bodies.size do throw s!"missing root body {root.bodyId}"
    roots := roots.push root.bodyId
    for child in root.promotedBodies do
      if let some bodyId := child.bodyId then
        unless bodyId < input.bodies.size do throw s!"missing promoted body {bodyId}"
        promoted := promoted.push (root.bodyId, child.index, bodyId)
  for inst in input.instances do
    if let some bodyId := inst.bodyId then
      unless bodyId < input.bodies.size do throw s!"missing instance body {bodyId}"
      instances := instances.push (inst.id, bodyId)
      for child in inst.promotedBodies do
        if let some childId := child.bodyId then
          unless childId < input.bodies.size do throw s!"missing promoted body {childId}"
          promoted := promoted.push (bodyId, child.index, childId)
  for (body, bodyId) in input.bodies.toList.zipIdx do
    for child in body.promotedBodies do
      if let some childId := child.bodyId then
        unless childId < input.bodies.size do throw s!"missing promoted body {childId}"
        let entry := (bodyId, child.index, childId)
        unless promoted.contains entry do promoted := promoted.push entry
  pure ⟨← lowerBodies (LowerContext.ofDocument input) (input.bodies.map Body.toBodyCore),
    roots, instances, promoted, input⟩



structure CompilerTables where
  spans : Array SourceSpanData
  definitions : Array DefinitionId
  typeConstants : Array MIR.TypeConst

def LoweredProgram.compilerTables (program : LoweredProgram) : CompilerTables :=
  ⟨program.bundle.spans, program.bundle.definitions, program.bundle.typeConstants⟩

def LoweredProgram.withCompilerTables (program : LoweredProgram) (tables : CompilerTables) : LoweredProgram :=
  let bodies := program.bundle.bodies.map fun body => { body with
    spans := tables.spans, definitions := tables.definitions, typeConstants := tables.typeConstants }
  { program with bundle := ⟨bodies, tables.spans, tables.definitions, tables.typeConstants⟩ }

def lowerCompilerGenericArgs (ctx : LowerContext) (tables : CompilerTables) (value : TypedValue) :
    LowerResult (Array MIR.GenericArg × CompilerTables) := do
  let (args, state) ← (genericArgs ctx value).run
    { spans := tables.spans, definitions := tables.definitions, typeConstants := tables.typeConstants }
  pure (args, ⟨state.spans, state.definitions, state.typeConstants⟩)

def lowerCompilerConstOperand (ctx : LowerContext) (tables : CompilerTables) (value : TypedValue) :
    LowerResult (MIR.ConstOperand × CompilerTables) := do
  let (operand, state) ← (constOperand ctx value).run
    { spans := tables.spans, definitions := tables.definitions, typeConstants := tables.typeConstants }
  pure (operand, ⟨state.spans, state.definitions, state.typeConstants⟩)

def lowerCompilerConstValue (ctx : LowerContext) (ty : MIR.TyId) (value : TypedValue) :
    LowerResult MIR.ConstValue := constValue ctx ty value


def lowerCompilerTypeConst (ctx : LowerContext) (tables : CompilerTables) (value : TypedValue) :
    LowerResult (MIR.TypeConstId × CompilerTables) := do
  let id ← typeConstRef ctx value
  unless id < tables.typeConstants.size do throw s!"missing type constant {id}"
  pure (id, tables)

/-- Intern a compiler span without synthesizing a source location. -/
def lowerCompilerSpan (tables : CompilerTables) (value : TypedValue) :
    LowerResult (MIR.SpanRef × CompilerTables) := do
  let (id, state) ← (spanRef value).run
    { spans := tables.spans, definitions := tables.definitions, typeConstants := tables.typeConstants }
  pure (id, ⟨state.spans, state.definitions, state.typeConstants⟩)

/-- Decode the source place key for compiler query evidence. Projection types
must already belong to the shared input type graph. -/
def lowerCompilerPlace (ctx : LowerContext) (value : TypedValue) : LowerResult MIR.Place :=
  place ctx value

end Miri.Input
