import Miri.Input.JsonReader
import Miri.Input.Model.Catalogs
import Miri.MIR.Syntax

namespace Miri.Input.DecodeMIR

open JsonReader
abbrev Result := Except String

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
  path : Miri.Interpreter.OperandPath := #[]
  threadLocal : Slice → Result Catalog.ThreadLocal := fun _ => .error "TLS metadata decoder unavailable"

private abbrev Fields := Array (String × Slice)
private abbrev DecodeM := StateT NodeFacts (ReaderT Context (Except String))

private def atField (name : String) (action : DecodeM α) : DecodeM α :=
  fun state ctx => action state {ctx with path := ctx.path.push (.field name)}

private def atIndex (index : Nat) (action : DecodeM α) : DecodeM α :=
  fun state ctx => action state {ctx with path := ctx.path.push (.index index)}

private def run (ctx : Context) (action : DecodeM α) : Result α :=
  (action.run {}).run ctx |>.map Prod.fst

private def runFacts (ctx : Context) (action : DecodeM α) : Result (α × NodeFacts) :=
  (action.run {}).run ctx

private def fields (v : Slice) : Result Fields := v.object
private def get (fs : Fields) (key : String) : Result Slice :=
  match fs.find? (·.1 == key) with
  | some (_, v) => pure v
  | none => throw s!"missing MIR field {key}"
private def nat (v : Slice) : Result Nat := v.natural
private def text (v : Slice) : Result String := v.string
private def bool (v : Slice) : Result Bool := v.boolean
private def array (v : Slice) : Result (Array Slice) := v.array
private def tag (v : Slice) : Result String :=
  match v.string with
  | .ok s => pure s
  | .error _ => do text (← v.field "kind")
private def optional (f : Slice → Result α) (v : Slice) : Result (Option α) :=
  if v.isNull then pure none else some <$> f v
private def optionalM (f : Slice → DecodeM α) (v : Slice) : DecodeM (Option α) :=
  if v.isNull then pure none else some <$> f v
private def number (v : Slice) : Result Nat :=
  match v.string with
  | .ok s => match s.toNat? with | some n => pure n | none => throw "invalid decimal integer"
  | .error _ => v.natural
private def typeId (ctx : Context) (v : Slice) : Result MIR.TyId := do
  let id ← nat v
  unless id < ctx.typeCount do throw s!"unresolved type {id}"
  pure id
private def definition (v : Slice) : DecodeM MIR.DefId := do
  let id ← nat v
  unless id < (← read).definitionCount do throw s!"unresolved definition {id}"
  pure id
private def spanRef (v : Slice) : DecodeM MIR.SpanRef := do
  let id ← nat v
  unless id < (← read).spanCount do throw s!"missing source span {id}"
  pure ⟨id⟩
private def source (v : Slice) : DecodeM MIR.SourceInfo := do
  let span ← spanRef (← v.field "span")
  let scope ← nat (← v.field "scope")
  unless scope < (← read).scopeCount do throw "unresolved source scope"
  pure ⟨span, scope⟩
private def Context.scalarSize (ctx : Context) (id : Nat) : Option Nat :=
  (ctx.scalarSizes[id]?).join

private def mutability (v : Slice) : Result MIR.Mutability := do
  match ← tag v with
  | "mutable" => pure .Mut
  | "immutable" => pure .Not
  | _ => throw "unknown mutability"

private def safety (v : Slice) : Result MIR.Safety := do
  match ← tag v with
  | "safe" => pure .Safe
  | "unsafe" => pure .Unsafe
  | _ => throw "unknown safety"

private def castKind (v : Slice) : Result MIR.CastKind := do
  let fs ← fields v
  match ← tag v with
  | "PointerExposeProvenance" => pure .PointerExposeProvenance
  | "PointerWithExposedProvenance" => pure .PointerWithExposedProvenance
  | "PointerCoercion" =>
    let c ← get fs "coercion"
    let cf ← fields c
    let coercion ← (show Result MIR.PointerCoercion from match ← tag c with
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

private def boundIndex (v : Slice) : Result MIR.BoundVarIndexKind := do
  let fs ← fields v
  match ← tag v with
  | "bound" => return .Bound (← nat (← get fs "debruijn_index"))
  | "canonical" => pure .Canonical
  | _ => throw "unknown bound index kind"

private def boundRegion (v : Slice) : DecodeM MIR.BoundRegionKind := do
  let fs ← fields v
  match ← tag v with
  | "anonymous" => pure .Anon
  | "named_for_printing" => return .NamedForPrinting (← text (← get fs "name"))
  | "named" => return .Named (← definition (← get fs "def_id"))
  | "closure_environment" => pure .ClosureEnv
  | _ => throw "unknown bound region kind"

private def region (v : Slice) : DecodeM MIR.Region := do
  let fs ← fields v
  match ← tag v with
  | "early_parameter" => return .EarlyParameter (← nat (← get fs "index")) (← text (← get fs "name"))
  | "bound" => return .Bound (← boundIndex (← get fs "index_kind")) (← nat (← get fs "variable_index")) (← boundRegion (← get fs "bound_kind"))
  | "late_parameter" =>
    let p ← get fs "parameter"
    let pf ← fields p
    let kind ← (show DecodeM MIR.LateParamRegionKind from match ← tag p with
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

private def borrow (v : Slice) : Result MIR.BorrowKind := do
  let fs ← fields v
  match ← tag v with
  | "shared" => pure .Shared
  | "fake" =>
    unless (← tag (← get fs "retag_mode")) == "default" do throw "unknown fake-borrow retag mode"
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

private def projection (ctx : Context) (v : Slice) : Result MIR.ProjectionElem := do
  let fs ← fields v
  match ← tag v with
  | "Deref" => pure .Deref
  | "Field" => return .Field (← nat (← get fs "index")) (← typeId ctx (← get fs "field_type"))
  | "Index" =>
    let id ← nat (← get fs "local")
    unless id < ctx.localCount do throw s!"out-of-range local {id}"
    pure (.Index id)
  | "ConstantIndex" => return .ConstantIndex (← nat (← get fs "offset")) (← nat (← get fs "min_length")) (← bool (← get fs "from_end"))
  | "Subslice" => return .Subslice (← nat (← get fs "from")) (← nat (← get fs "to")) (← bool (← get fs "from_end"))
  | "Downcast" =>
    let name ← optional text (← get fs "name")
    return .Downcast name (← nat (← get fs "variant_index"))
  | "OpaqueCast" => return .OpaqueCast (← typeId ctx (← get fs "cast_type"))
  | "UnwrapUnsafeBinder" => return .UnwrapUnsafeBinder (← typeId ctx (← get fs "inner_type"))
  | "PhantomDeref" => pure .PhantomDeref
  | _ => throw "unknown projection"

private def place (ctx : Context) (v : Slice) : DecodeM MIR.Place := do
  let fs ← fields v
  let id ← nat (← get fs "local")
  unless id < ctx.localCount do throw s!"out-of-range local {id}"
  let projections ← array (← get fs "projection")
  let value : MIR.Place := ⟨id, ← (projections.mapM (projection ctx) : Result _)⟩
  let path := (← read).path
  let fact : PlaceFact := ⟨path, value, ← typeId ctx (← get fs "type"),
    ← (projections.mapM fun item => do typeId ctx (← item.field "resulting_type") : Result _)⟩
  modify fun facts => { facts with places := facts.places.push fact }
  return value

private def binOp (v : Slice) : Result MIR.BinOp := do
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

private def unOp (v : Slice) : Result MIR.UnOp := do
  match ← tag v with
    | "not" => pure .Not
    | "negate" => pure .Neg
    | "pointer_metadata" => pure .PtrMetadata
    | _ => throw "unknown unary operator"

private def typeConstRef (ctx : Context) (value : Slice) : Result MIR.TypeConstId := do
  let id ← nat value
  unless id < ctx.typeConstantCount do throw s!"unresolved type constant {id}"
  pure id

private def genericArgs (ctx : Context) (v : Slice) : DecodeM (Array MIR.GenericArg) := do
  (← array v).mapM fun arg => do
    let fs ← fields arg
    match ← tag arg with
    | "type" => return .Type (← typeId ctx (← get fs "value"))
    | "lifetime" => return .Lifetime (← region (← get fs "value"))
    | "const" => return .Const (← typeConstRef ctx (← get fs "value"))
    | _ => throw "unknown generic argument"


private def annotation (v : Slice) : Result Nat :=
  match nat v with
  | .ok n => pure n
  | .error _ => do let fs ← fields v; nat (← get fs "index")

private def aggregate (ctx : Context) (v : Slice) : DecodeM MIR.AggregateKind := do
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

private def allocationId (ctx : Context) (v : Slice) : Result MIR.AllocationId := do
  let id ← nat v
  unless id < ctx.allocationCount do throw s!"unresolved allocation {id}"
  pure id

private def constValue (ctx : Context) (ty : MIR.TyId) (v : Slice) : Result MIR.ConstValue := do
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

private def constOperand (ctx : Context) (v : Slice) : DecodeM MIR.ConstOperand := do
  let c ← fields v
  let ty ← typeId ctx (← get c "type")
  let userType ← optional annotation (← get c "user_type_annotation")
  let span ← spanRef (← get c "span")
  let evaluatedValue ← get c "constant"
  unless (← tag evaluatedValue) == "evaluated_const" do throw "unknown constant evaluation record"
  let evaluated ← fields evaluatedValue
  let originalValue ← get evaluated "source"
  let original ← fields originalValue
  let constant ← (show DecodeM MIR.MirConst from match ← tag originalValue with
    | "already_evaluated" => return .Val (← constValue ctx ty (← get evaluated "value")) ty
    | "type_system_const" => return .Ty (← typeId ctx (← get original "type")) (← typeConstRef ctx (← get original "const"))
    | "unevaluated" => return .Unevaluated ⟨← definition (← get original "def_id"), ← genericArgs ctx (← get original "generic_args"), ← optional nat (← get original "promoted")⟩ (← typeId ctx (← get original "type"))
    | _ => throw "unknown MIR constant source")
  let value : MIR.ConstOperand := ⟨span, userType, constant⟩
  let evaluated ← constValue ctx ty (← get evaluated "value")
  let path := (← read).path
  modify fun facts => { facts with constants := facts.constants.push ⟨path, value, ty, evaluated⟩ }
  pure value

private def operand (ctx : Context) (v : Slice) : DecodeM MIR.Operand := do
  let fs ← fields v
  match ← tag v with
  | "Copy" => return .Copy (← atField "place" (place ctx (← get fs "place")))
  | "Move" => return .Move (← atField "place" (place ctx (← get fs "place")))
  | "RuntimeChecks" =>
    let rawCheck ← get fs "check"
    let _ ← bool (← rawCheck.field "enabled")
    let check ← tag rawCheck
    let check ← match check with
      | "ub_checks" => pure MIR.RuntimeChecks.UbChecks
      | "contract_checks" => pure .ContractChecks
      | "overflow_checks" => pure .OverflowChecks
      | _ => throw "unknown runtime check"
    return .RuntimeChecks check
  | "Constant" => return .Constant (← atField "constant" (constOperand ctx (← get fs "constant")))
  | _ => throw "unknown operand"

private def captureUpcast (ctx : Context) (v : Slice) (kind : MIR.CastKind) : DecodeM Unit := do
  let some desc ← v.optionalField "vtable_allocation" | return
  if desc.isNull then return
  if (← tag desc) != "dynamic_vtable_upcast" then return
  match kind with
  | .PointerCoercion .Unsize _ => pure ()
  | _ => throw "dynamic vtable descriptor requires an unsizing cast"
  let operand ← v.field "operand"
  let operandType ← match ← tag operand with
    | "Copy" | "Move" => typeId ctx (← (← operand.field "place").field "type")
    | "Constant" => typeId ctx (← (← operand.field "constant").field "type")
    | _ => throw "dynamic vtable upcast lacks operand type"
  let query ← desc.field "supertrait_slot_query"
  unless (← text (← desc.field "runtime_vtable")) == "source_operand_metadata" &&
      (← text (← query.field "query_kind")) == "supertrait_slot" &&
      (← text (← query.field "typing_env")) == "fully_monomorphized" do
    throw "invalid dynamic vtable query metadata"
  let evidence : DynamicUpcastEvidence := {
    operandType, castTarget := ← typeId ctx (← v.field "target_type"),
    sourceType := ← typeId ctx (← desc.field "source_type"),
    targetType := ← typeId ctx (← desc.field "target_type"),
    sourcePointeeType := ← typeId ctx (← desc.field "source_pointee_type"),
    targetPointeeType := ← typeId ctx (← desc.field "target_pointee_type"),
    sourceTailType := ← typeId ctx (← desc.field "source_tail_type"),
    targetTailType := ← typeId ctx (← desc.field "target_tail_type"),
    querySource := ← typeId ctx (← query.field "input_source"),
    queryTarget := ← typeId ctx (← query.field "input_target") }
  modify fun facts => {facts with dynamicUpcasts := facts.dynamicUpcasts.push evidence}

private def rvalue (ctx : Context) (v : Slice) : DecodeM MIR.Rvalue := do
  let fs ← fields v
  match ← tag v with
  | "Use" =>
    let rawRetag ← get fs "retag"
    let retag ← tag rawRetag
    unless (← bool (← rawRetag.field "performs_retag")) == (retag == "yes") do
      throw "WithRetag boolean disagrees with tag"
    let retag ← match retag with
      | "yes" => pure MIR.WithRetag.Yes
      | "no" => pure .No
      | _ => throw "unknown retag mode"
    return .Use (← atField "operand" (operand ctx (← get fs "operand"))) retag
  | "BinaryOp" =>
    let op ← binOp (← get fs "operator")
    return .BinaryOp op (← atField "left" (operand ctx (← get fs "left"))) (← atField "right" (operand ctx (← get fs "right")))
  | "UnaryOp" =>
    let op ← unOp (← get fs "operator")
    return .UnaryOp op (← atField "operand" (operand ctx (← get fs "operand")))
  | "Discriminant" => return .Discriminant (← atField "place" (place ctx (← get fs "place")))
  | "CopyForDeref" => return .CopyForDeref (← atField "place" (place ctx (← get fs "place")))
  | "WrapUnsafeBinder" => return .WrapUnsafeBinder (← atField "operand" (operand ctx (← get fs "operand"))) (← typeId ctx (← get fs "type"))
  | "Repeat" => return .Repeat (← atField "operand" (operand ctx (← get fs "operand"))) (← typeConstRef ctx (← get fs "count"))
  | "Ref" => return .Ref (← region (← get fs "region")) (← borrow (← get fs "borrow_kind")) (← atField "place" (place ctx (← get fs "place")))
  | "ThreadLocalRef" =>
    let entry ← ctx.threadLocal v
    modify fun facts => { facts with threadLocals := facts.threadLocals.push entry }
    return .ThreadLocalRef (← definition (← get fs "def_id"))
  | "RawPtr" =>
    let kind ← (show DecodeM MIR.RawPtrKind from match ← tag (← get fs "pointer_kind") with
      | "mutable" => pure .Mut
      | "constant" => pure .Const
      | "metadata_only" => pure .FakeForPtrMetadata
      | _ => throw "unknown raw pointer kind")
    return .RawPtr kind (← atField "place" (place ctx (← get fs "place")))
  | "Cast" =>
    let kind ← castKind (← get fs "cast_kind")
    captureUpcast ctx v kind
    return .Cast kind (← atField "operand" (operand ctx (← get fs "operand"))) (← typeId ctx (← get fs "target_type"))
  | "Aggregate" => return .Aggregate (← aggregate ctx (← get fs "aggregate_kind")) (← atField "operands" ((← array (← get fs "operands")).mapIdxM fun i v => atIndex i (operand ctx v)))
  | "Reborrow" => return .Reborrow (← typeId ctx (← get fs "type")) (← mutability (← get fs "mutability")) (← atField "place" (place ctx (← get fs "place")))
  | _ => throw "unknown rvalue"

private def fakeRead (v : Slice) : DecodeM MIR.FakeReadCause := do
  let fs ← fields v
  match ← tag v with
  | "match_guard" => pure .ForMatchGuard
  | "matched_place" => return .ForMatchedPlace (← optionalM definition (← get fs "hoisted_from"))
  | "guard_binding" => pure .ForGuardBinding
  | "let_binding" => return .ForLet (← optionalM definition (← get fs "hoisted_from"))
  | "index" => pure .ForIndex
  | _ => throw "unknown fake read cause"

private def variance (v : Slice) : Result MIR.Variance := do
  match ← tag v with
  | "covariant" => pure .Covariant
  | "contravariant" => pure .Contravariant
  | "invariant" => pure .Invariant
  | "bivariant" => pure .Bivariant
  | _ => throw "unknown variance"

private def userProjectionKind (v : Slice) : Result MIR.ProjectionKind := do
  let fs ← fields v
  match ← tag v with
  | "Deref" => pure .Deref
  | "Field" => return .Field (← nat (← get fs "index"))
  | "Index" => pure .Index
  | "ConstantIndex" => return .ConstantIndex (← nat (← get fs "offset")) (← nat (← get fs "min_length")) (← bool (← get fs "from_end"))
  | "Subslice" => return .Subslice (← nat (← get fs "from")) (← nat (← get fs "to")) (← bool (← get fs "from_end"))
  | "Downcast" => return .Downcast (← optional text (← get fs "name")) (← nat (← get fs "variant_index"))
  | "OpaqueCast" => pure .OpaqueCast
  | "UnwrapUnsafeBinder" => pure .UnwrapUnsafeBinder
  | "PhantomDeref" => pure .PhantomDeref
  | _ => throw "unknown user projection"

private def userProjection (v : Slice) : Result MIR.UserTypeProjection := do
  let fs ← fields v
  return ⟨← nat (← get fs "base_index"), ← (← array (← get fs "projections")).mapM userProjectionKind⟩

private def coverage (v : Slice) : DecodeM MIR.CoverageKind := do
  let fs ← fields v
  match ← tag v with
  | "point" =>
    let kind ← (show DecodeM MIR.CoveragePointKind from match ← tag (← get fs "point_kind") with
      | "expr" => pure .Expr
      | "implicit_else" => pure .ImplicitElse
      | "function_end" => pure .FunctionEnd
      | _ => throw "unknown coverage point")
    let hir ← fields (← get fs "hir_id")
    return .Point kind ⟨← definition (← get hir "owner_def_id"), ← nat (← get hir "local_id")⟩
  | "block_marker" => return .BlockMarker (← nat (← get fs "id"))
  | "virtual_counter" => return .VirtualCounter (← nat (← get fs "bcb"))
  | _ => throw "unknown coverage kind"

private def statement (ctx : Context) (node : Slice) : DecodeM MIR.Statement := do
  let kind ← (show DecodeM MIR.StatementKind from do
    let fs ← fields (← node.field "kind")
    match ← text (← get fs "variant") with
    | "Assign" => return MIR.StatementKind.Assign (← atField "place" (place ctx (← get fs "place"))) (← atField "rvalue" (rvalue ctx (← get fs "rvalue")))
    | "StorageLive" => return .StorageLive (← nat (← get fs "local"))
    | "StorageDead" => return .StorageDead (← nat (← get fs "local"))
    | "PlaceMention" => return .PlaceMention (← atField "place" (place ctx (← get fs "place")))
    | "SetDiscriminant" => return .SetDiscriminant (← atField "place" (place ctx (← get fs "place"))) (← nat (← get fs "variant_index"))
    | "ConstEvalCounter" => pure .ConstEvalCounter
    | "Nop" => pure .Nop
    | "FakeRead" => return .FakeRead (← fakeRead (← get fs "cause")) (← atField "place" (place ctx (← get fs "place")))
    | "AscribeUserType" => return .AscribeUserType (← atField "place" (place ctx (← get fs "place"))) (← userProjection (← get fs "user_type_projection")) (← variance (← get fs "variance"))
    | "Coverage" => return .Coverage (← coverage (← get fs "coverage"))
    | "Intrinsic" =>
      let intrinsic ← (show DecodeM MIR.NonDivergingIntrinsic from match ← text (← get fs "intrinsic") with
        | "Assume" => return .Assume (← atField "value" (operand ctx (← get fs "value")))
        | "CopyNonOverlapping" => return .CopyNonOverlapping ⟨← atField "src" (operand ctx (← get fs "src")), ← atField "dst" (operand ctx (← get fs "dst")), ← atField "count" (operand ctx (← get fs "count"))⟩
        | _ => throw "unknown nondiverging intrinsic")
      pure (.Intrinsic intrinsic)
    | "BackwardIncompatibleDropHint" =>
      unless (← tag (← get fs "reason")) == "edition_2024" do throw "unknown backward drop reason"
      return .BackwardIncompatibleDropHint (← atField "place" (place ctx (← get fs "place"))) .Edition2024
    | _ => throw "unknown statement")
  return ⟨← source (← node.field "source_info"), kind⟩

private def unwindReason (v : Slice) : Result MIR.UnwindTerminateReason := do
  match ← tag v with
  | "abi" => pure .Abi
  | "in_cleanup" => pure .InCleanup
  | _ => throw "unknown unwind termination reason"

private def coroutine (v : Slice) : Result MIR.CoroutineKind := do
  let fs ← fields v
  match ← tag v with
  | "desugared" =>
    let desugaring ← (show Result MIR.CoroutineDesugaring from match ← text (← get fs "desugaring") with
      | "async" => pure .Async
      | "gen" => pure .Gen
      | "async_gen" => pure .AsyncGen
      | _ => throw "unknown coroutine desugaring")
    let source ← (show Result MIR.CoroutineSource from match ← text (← get fs "source") with
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

private def unwind (v : Slice) : Result MIR.UnwindAction := do
  let fs ← fields v
  match ← text (← get fs "kind") with
  | "Continue" => pure .Continue
  | "Unreachable" => pure .Unreachable
  | "Cleanup" => return .Cleanup (← nat (← get fs "target"))
  | "Terminate" => return .Terminate (← unwindReason (← get fs "reason"))
  | _ => throw "unknown unwind action"

private def assertKind (ctx : Context) (v : Slice) : DecodeM MIR.AssertKind := do
  let fs ← fields v
  match ← tag v with
  | "Overflow" =>
    let op ← binOp (← get fs "operator")
    return .Overflow op (← atField "left" (operand ctx (← get fs "left"))) (← atField "right" (operand ctx (← get fs "right")))
  | "BoundsCheck" => return .BoundsCheck (← atField "length" (operand ctx (← get fs "length"))) (← atField "index" (operand ctx (← get fs "index")))
  | "OverflowNeg" => return .OverflowNeg (← atField "operand" (operand ctx (← get fs "operand")))
  | "DivisionByZero" => return .DivisionByZero (← atField "operand" (operand ctx (← get fs "operand")))
  | "RemainderByZero" => return .RemainderByZero (← atField "operand" (operand ctx (← get fs "operand")))
  | "NullPointerDereference" => pure .NullPointerDereference
  | "NullReferenceConstructed" => pure .NullReferenceConstructed
  | "ResumedAfterReturn" => return .ResumedAfterReturn (← coroutine (← get fs "coroutine_kind"))
  | "ResumedAfterPanic" => return .ResumedAfterPanic (← coroutine (← get fs "coroutine_kind"))
  | "ResumedAfterDrop" => return .ResumedAfterDrop (← coroutine (← get fs "coroutine_kind"))
  | "MisalignedPointerDereference" => return .MisalignedPointerDereference (← atField "required" (operand ctx (← get fs "required"))) (← atField "found" (operand ctx (← get fs "found")))
  | "InvalidEnumConstruction" => return .InvalidEnumConstruction (← atField "operand" (operand ctx (← get fs "operand")))
  | _ => throw "unknown assertion kind"

private def loopHint (v : Slice) : Result MIR.LoopHintAttr := do
  let fs ← fields v
  match ← text (← get fs "kind") with
  | "Hint" => pure .Hint
  | "Full" => pure .Full
  | "Never" => pure .Never
  | "Count" => return .Count (← nat (← get fs "count"))
  | _ => throw "unknown loop hint"

private def callSource (v : Slice) : Result MIR.CallSource := do
  match ← tag v with
  | "overloaded_operator" => pure .OverloadedOperator
  | "match_comparison" => pure .MatchCmp
  | "miscellaneous_desugaring" => pure .Misc
  | "clone_or_use" => pure .Use
  | "normal_call" => pure .Normal
  | _ => throw "unknown call source"

private def spannedOperand (ctx : Context) (v : Slice) : DecodeM MIR.SpannedOperand := do
  let fs ← fields v
  return ⟨← spanRef (← get fs "span"), ← atField "operand" (operand ctx (← get fs "operand"))⟩

private def asmArch (v : Slice) : Result MIR.InlineAsmArch := do
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

private def asmRegister (v : Slice) : Result MIR.InlineAsmRegOrRegClass := do
  let fs ← fields v
  let arch ← asmArch (← get fs "arch")
  let name ← text (← get fs "name")
  match ← tag v with
  | "register" => pure (.Reg arch name)
  | "register_class" => pure (.RegClass arch name)
  | _ => throw "unknown assembly register kind"

private def asmPiece (v : Slice) : DecodeM MIR.InlineAsmTemplatePiece := do
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

private def asmOperand (ctx : Context) (v : Slice) : DecodeM MIR.InlineAsmOperand := do
  let fs ← fields v
  match ← tag v with
  | "in" => return .In (← asmRegister (← get fs "register")) (← atField "value" (operand ctx (← get fs "value")))
  | "out" => return .Out (← asmRegister (← get fs "register")) (← bool (← get fs "late")) (← atField "place" (optionalM (place ctx) (← get fs "place")))
  | "inout" => return .InOut (← asmRegister (← get fs "register")) (← bool (← get fs "late")) (← atField "input" (operand ctx (← get fs "input"))) (← atField "output" (optionalM (place ctx) (← get fs "output")))
  | "const" => return .Const (← atField "value" (constOperand ctx (← get fs "value")))
  | "sym_fn" => return .SymFn (← atField "value" (constOperand ctx (← get fs "value")))
  | "sym_static" => return .SymStatic (← definition (← get fs "def_id"))
  | "label" => return .Label (← nat (← get fs "target_index"))
  | _ => throw "unknown assembly operand"

private def inlineAsm (ctx : Context) (fs : Fields) : DecodeM MIR.InlineAsmTerminator := do
  let macroKind ← (show DecodeM MIR.InlineAsmMacro from match ← text (← get fs "asm_macro") with
    | "asm" => pure .Asm
    | "naked_asm" => pure .NakedAsm
    | _ => throw "unknown assembly macro")
  let options ← fields (← get fs "options")
  let options : MIR.InlineAsmOptions := ⟨← bool (← get options "pure"), ← bool (← get options "nomem"),
    ← bool (← get options "readonly"), ← bool (← get options "preserves_flags"), ← bool (← get options "noreturn"),
    ← bool (← get options "nostack"), ← bool (← get options "att_syntax"), ← bool (← get options "raw"), ← bool (← get options "may_unwind")⟩
  let template ← (← array (← get fs "template")).mapM asmPiece
  let operands ← atField "operands" ((← array (← get fs "operands")).mapIdxM fun i v => atIndex i (asmOperand ctx v))
  let spans ← (← array (← get fs "line_spans")).mapM spanRef
  let targets ← ((← array (← get fs "targets")).mapM nat : Result _)
  for op in operands do
    match op with
    | .Label index => unless index < targets.size do throw "assembly label index exceeds target list"
    | _ => pure ()
  for piece in template do
    match piece with
    | .Placeholder index _ _ => unless index < operands.size do throw "assembly placeholder exceeds operand list"
    | _ => pure ()
  return ⟨macroKind, template, operands, options, spans, targets, ← unwind (← get fs "unwind")⟩

private def terminator (ctx : Context) (node : Slice) : DecodeM MIR.Terminator := do
  let kind ← (show DecodeM MIR.TerminatorKind from do
    let fs ← fields (← node.field "kind")
    match ← text (← get fs "variant") with
    | "Return" => pure MIR.TerminatorKind.Return
    | "Unreachable" => pure .Unreachable
    | "UnwindResume" => pure .UnwindResume
    | "CoroutineDrop" => pure .CoroutineDrop
    | "Assert" => return .Assert (← atField "condition" (operand ctx (← get fs "condition"))) (← bool (← get fs "expected")) (← atField "message" (assertKind ctx (← get fs "message"))) (← nat (← get fs "target")) (← unwind (← get fs "unwind"))
    | "FalseEdge" => return .FalseEdge (← nat (← get fs "real_target")) (← nat (← get fs "imaginary_target"))
    | "Goto" =>
      let hints ← array (← get fs "loop_hints")
      let lowered ← (hints.mapM loopHint : Result _ )
      return .Goto (← nat (← get fs "target")) lowered
    | "SwitchInt" =>
      let cases ← (← array (← get fs "targets")).mapM fun entry => do
        let ef ← fields entry
        pure (MIR.SwitchTarget.Case (← number (← get ef "value")) (← nat (← get ef "target")))
      return .SwitchInt (← atField "discriminant" (operand ctx (← get fs "discriminant"))) ⟨cases, ← nat (← get fs "otherwise")⟩
    | "UnwindTerminate" => return .UnwindTerminate (← unwindReason (← get fs "reason"))
    | "Drop" => return .Drop (← atField "place" (place ctx (← get fs "place"))) (← nat (← get fs "target")) (← unwind (← get fs "unwind")) (← bool (← get fs "replace")) (← optional nat (← get fs "async_drop"))
    | "Call" => return .Call (← atField "function" (operand ctx (← get fs "function"))) (← atField "args" ((← array (← get fs "args")).mapIdxM fun i v => atIndex i (spannedOperand ctx v))) (← atField "destination" (place ctx (← get fs "destination"))) (← optional nat (← get fs "target")) (← unwind (← get fs "unwind")) (← callSource (← get fs "call_source")) (← spanRef (← get fs "function_span"))
    | "TailCall" => return .TailCall (← atField "function" (operand ctx (← get fs "function"))) (← atField "args" ((← array (← get fs "args")).mapIdxM fun i v => atIndex i (spannedOperand ctx v))) (← spanRef (← get fs "function_span"))
    | "Yield" => return .Yield (← atField "value" (operand ctx (← get fs "value"))) (← nat (← get fs "resume")) (← atField "resume_arg" (place ctx (← get fs "resume_arg"))) (← optional nat (← get fs "drop"))
    | "FalseUnwind" => return .FalseUnwind (← nat (← get fs "real_target")) (← unwind (← get fs "unwind"))
    | "InlineAsm" => return .InlineAsm (← inlineAsm ctx fs)
    | _ => throw "unknown terminator")
  return ⟨← source (← node.field "source_info"), kind⟩

private def phase (v : Slice) : Result MIR.MirPhase := do
  let fs ← fields v
  match ← tag v with
  | "built" =>
    unless (← v.optionalField "phase").isNone do throw "built MIR phase has a subphase"
    pure .Built
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



private def optionalField (v : Slice) (key : String) (f : Slice → Result α) : Result (Option α) := do
  match ← v.optionalField key with
  | none => pure none
  | some value => optional f value

private def sourceInfo (ctx : Context) (v : Slice) : Result SourceInfo := do
  let info ← run ctx (source v)
  pure ⟨info.span.id, info.scope⟩

private def scope (ctx : Context) (v : Slice) : Result SourceScope := do
  let inlined ← optionalField v "inlined" fun value => do
    return { instanceId := ← nat (← value.field "instance_id")
             callsiteSpanId := ← nat (← value.field "callsite_span")
             requiresCallerLocation := ← bool (← value.field "requires_caller_location") }
  let id ← nat (← v.field "scope")
  let spanId ← nat (← v.field "span")
  unless spanId < ctx.spanCount do throw s!"unresolved scope span {spanId}"
  return { id, spanId, inlined, parent := ← optionalField v "parent" nat,
           inlinedParent := ← optionalField v "inlined_parent_scope" nat }

private def backtrace (ctx : Context) (v : Slice) : Result BacktraceSpan := do
  let spanId ← nat (← v.field "span")
  unless spanId < ctx.spanCount do throw s!"unresolved backtrace span {spanId}"
  let pos ← v.field "source_position"
  return { spanId, collapsedLo := ← nat (← v.field "collapsed_lo"), position := {
    bytePosition := ← nat (← pos.field "byte_position"), line := ← nat (← pos.field "line"),
    column := ← nat (← pos.field "zero_based_char_column"), filename := ← text (← pos.field "filename") } }

private def callEvidence (ctx : Context) (v : Slice) : Result CallResolutionEvidence := do
  let kind ← match ← tag v with
    | "resolved_instance" => pure CallResolutionKind.direct
    | "virtual_dispatch" => pure .virtualDispatch
    | "indirect_function_pointer" => pure .indirect
    | _ => throw "unknown call resolution"
  let instanceId ← if kind == .indirect then pure none else some <$> nat (← v.field "instance_id")
  let functionType ← typeId ctx (← v.field "function_type")
  let dispatchSlot ← if kind == .virtualDispatch then some <$> nat (← v.field "dispatch_slot") else pure none
  pure {kind, instanceId, functionType := some functionType, dispatchSlot, fnAbiId := ← nat (← v.field "fn_abi")}

private def constantContext (ctx : Context) (v : Slice) : Result ConstantQueryContext := do
  let inputPhase ← match ← text (← v.field "mir_input_phase") with
    | "template" => pure BodyInputPhase.template
    | "already_instantiated" => pure .alreadyInstantiated
    | _ => throw "unknown body input phase"
  let required ← v.field "required_constant_checks"
  let requiredChecks ← (← array (← required.field "checks")).mapM fun check => do
    let result ← check.field "result"
    let rawOperand ← result.field "normalized_operand"
    let normalizedOperand ← run ctx (constOperand ctx rawOperand)
    let ty ← typeId ctx (← rawOperand.field "type")
    let index ← nat (← check.field "index")
    let spanId ← nat (← check.field "span")
    let value ← constValue ctx ty (← result.field "value")
    return ({ index, spanId, normalizedOperand, value } : RequiredConstantCheck)
  return {
    inputPhase, requiredChecks, instanceId := ← nat (← v.field "instance_id"),
    normalizationBodyId := ← nat (← (← v.field "normalization").field "body"),
    requiredTypingEnvironment := ← text (← required.field "typing_env") }

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

/-- Pool metadata is decoded before bodies so scalar constants use compiler byte widths. -/
def decodeBody (ctx : Context) (v : Slice) (sourcePath : String) : Result Body := do
  let locals ← array (← v.field "locals")
  let blocks ← array (← v.field "basic_blocks")
  let scopes ← array (← v.field "source_scopes")
  let ctx := {ctx with localCount := locals.size, blockCount := blocks.size, scopeCount := scopes.size}
  unless !blocks.isEmpty do throw "body has no entry basic block"
  let sourceScopes ← scopes.mapM (scope ctx)
  for (item, i) in sourceScopes.toList.zipIdx do
    unless item.id == i do throw "noncontiguous source scopes"
    for parent in item.parent.toArray ++ item.inlinedParent.toArray do
      unless parent < sourceScopes.size do throw "unresolved parent source scope"
  let mut localTypes := #[]
  let mut localSources := #[]
  for (localDecl, i) in locals.toList.zipIdx do
    unless (← nat (← localDecl.field "local")) == i do throw "noncontiguous local IDs"
    localTypes := localTypes.push (← typeId ctx (← localDecl.field "type"))
    localSources := localSources.push (← sourceInfo ctx (← localDecl.field "source_info"))
  let mut decodedBlocks : Array MIR.BasicBlock := #[]
  let mut callEvidenceRows := #[]
  let mut nodeFacts := #[]
  for (block, i) in blocks.toList.zipIdx do
    unless (← nat (← block.field "block")) == i do throw "noncontiguous basic block IDs"
    let statements ← array (← block.field "statements")
    let decoded ← statements.mapM fun node => runFacts {ctx with path := #[.field "kind"]} (statement ctx node)
    let decodedStatements := decoded.map Prod.fst
    let rawTerminator ← block.field "terminator"
    let (term, termFacts) ← runFacts {ctx with path := #[.field "kind"]} (terminator ctx rawTerminator)
    for target in controlTargets term.kind do
      unless target < blocks.size do throw s!"out-of-range control-flow target {target}"
    for stmt in decodedStatements do
      match stmt.kind with
      | .StorageLive localId | .StorageDead localId =>
        unless localId < locals.size do throw s!"out-of-range local {localId}"
      | _ => pure ()
    let termKind ← rawTerminator.field "kind"
    let termTag ← text (← termKind.field "variant")
    let evidence ← if termTag == "Call" || termTag == "TailCall" then
      some <$> callEvidence ctx (← termKind.field "resolution") else pure none
    callEvidenceRows := callEvidenceRows.push evidence
    nodeFacts := nodeFacts.push ((decoded.map Prod.snd).push termFacts)
    decodedBlocks := decodedBlocks.push ⟨decodedStatements, term, ← bool (← block.field "is_cleanup")⟩
  let phase ← phase (← v.field "phase")
  let injectionPhase ← optionalField v "injection_phase" DecodeMIR.phase
  let argumentCount ← nat (← v.field "arg_count")
  unless argumentCount < locals.size do throw "argument count exceeds locals"
  let spreadArgument ← optionalField v "spread_arg" nat
  if let some index := spreadArgument then
    unless index > 0 && index ≤ argumentCount do throw "invalid spread argument"
  let definitionId ← match ← optionalField v "def_id" nat with
    | some id => pure (some id)
    | none => optionalField v "source_def_id" nat
  if let some id := definitionId then
    unless id < ctx.definitionCount do throw s!"unresolved definition {id}"
  let spanId ← nat (← v.field "span")
  let preambleDefSpanId ← nat (← v.field "preamble_def_span")
  unless spanId < ctx.spanCount && preambleDefSpanId < ctx.spanCount do throw "unresolved body span"
  let requiredConsts ← optionalField v "required_consts" fun raw => do
    (← array raw).mapM fun item => run ctx (constOperand ctx item)
  let promotedBodies ← match ← v.optionalField "promoted_bodies" with
    | none => pure #[]
    | some raw => (← array raw).mapM fun item => do
      pure { index := (← optionalField item "promoted_index" nat).getD 0,
             bodyId := ← optionalField item "body" nat : PromotedBody }
  let mir : MIR.Body := ⟨phase, argumentCount, spreadArgument, localTypes, decodedBlocks⟩
  pure {
    mir,
    definitionId, defPath := (← optionalField v "def_path" text).getD sourcePath, sourcePath,
    spanId, preambleDefSpanId, injectionPhase, isPolymorphic := ← optionalField v "is_polymorphic" bool, localSources, sourceScopes,
    backtraceSpans := ← (← array (← v.field "backtrace_spans")).mapM (backtrace ctx),
    callEvidence := callEvidenceRows, nodeFacts, requiredConsts,
    constantQueryContext := ← optionalField v "constant_query_context" (constantContext ctx), promotedBodies }

def decodeGenericArgs (ctx : Context) (v : Slice) : Result (Array MIR.GenericArg) :=
  run ctx (genericArgs ctx v)

def decodeConstOperand (ctx : Context) (v : Slice) : Result MIR.ConstOperand :=
  run ctx (constOperand ctx v)

def decodeConstValue (ctx : Context) (ty : MIR.TyId) (v : Slice) : Result MIR.ConstValue :=
  constValue ctx ty v

def decodePlace (ctx : Context) (v : Slice) : Result MIR.Place := run ctx (place ctx v)

end Miri.Input.DecodeMIR
