import Miri.Input.Model.SourceMir
import Miri.Frontend.Foundation
import Miri.Frontend.FoundationSpanRegistry
import Miri.Frontend.FoundationSourceTypes

/-! Decoder-only generic MIR ingestion. Unknown syntax becomes an unsupported
constructor in the typed body; malformed known references fail immediately.
The resulting data contain no JSON and no instantiated compiler answers. -/
namespace Miri.Frontend.Foundation.SourceMirParser
open Lean Miri Input.SourceMir

structure Context where
  types : Nat
  definitions : Nat
  locals : Nat
  blocks : Nat
  scopes : Nat
  allocations : Nat
  physical : Option Input.SourceTypes.Material := none

private def typeRef (c : Context) (id : Nat) : Except String Nat := do
  unless id < c.types do throw "source MIR type reference out of bounds"
  return id
private def definitionRef (c : Context) (id : Nat) : Except String Nat := do
  unless id < c.definitions do throw "source MIR definition reference out of bounds"
  return id
private def allocationRef (c : Context) (id : Nat) : Except String Nat := do
  unless id < c.allocations do throw "source MIR allocation reference out of bounds"
  return id
private def localRef (c : Context) (id : Nat) : Except String Nat := do
  unless id < c.locals do throw "source MIR local reference out of bounds"
  return id
private def blockRef (c : Context) (id : Nat) : Except String Nat := do
  unless id < c.blocks do throw "source MIR block reference out of bounds"
  return id
private def optionalNat (j : Json) (key : String) : Except String (Option Nat) :=
  j.getObjValAs? (Option Nat) key
private def spanKey (j : Json) : Except String SpanKey := do
  let result : SpanKey := ⟨← j.getObjValAs? Nat "lo",← j.getObjValAs? Nat "hi",
    ← j.getObjValAs? String "ctxt",← optionalNat j "parent_local_definition"⟩
  unless result.lo ≤ result.hi && result.hi < 2^32 do throw "source MIR span bounds invalid"
  return result
private def constantExpr (c : Context) (j : Json) : Except String Input.SourceTypes.ConstExpr := do
  let result ← SourceTypesParser.constant j
  match result with
  | .parameter _ ty => if let some ty := ty then let _ ← typeRef c ty; pure ()
  | .value ty bits bytes =>
    let _ ← typeRef c ty
    unless bytes ≤ 16 && bits < 2^(8*bytes) do throw "source MIR type constant bits/width invalid"
  | .alias id =>
    let some physical := c.physical | throw "source MIR const alias universe unavailable"
    unless id < physical.constantAliases.size do throw "source MIR const alias reference absent"
  | .unsupported _ => pure ()
  return result
private def arguments (c : Context) (j : Json) : Except String (Array Input.SourceTypes.Argument) := do
  let result ← (← j.getArr?).mapM SourceTypesParser.argument
  for arg in result do
    match arg with
    | .type ty => let _ ← typeRef c ty; pure ()
    | .constant (.value ty _ _) => let _ ← typeRef c ty; pure ()
    | .constant (.parameter _ (some ty)) => let _ ← typeRef c ty; pure ()
    | _ => pure ()
  return result

private def place (c : Context) (j : Json) : Except String Place := do
  let localId ← localRef c (← j.getObjValAs? Nat "local")
  let projection ← (← j.getObjValAs? (Array Json) "projection").mapM fun p => do
    match ← p.getObjValAs? String "kind" with
    | "deref" => pure Projection.deref
    | "field" => return .field (← p.getObjValAs? Nat "index") (← typeRef c (← p.getObjValAs? Nat "type"))
    | "index" => return .index (← localRef c (← p.getObjValAs? Nat "local"))
    | "downcast" => return .downcast (← p.getObjValAs? (Option String) "name") (← p.getObjValAs? Nat "variant")
    | tag => pure (.unsupported tag)
  return ⟨localId,projection⟩
def constant (c : Context) (j : Json) : Except String Constant := do
  let type ← typeRef c (← j.getObjValAs? Nat "type")
  let value ← j.getObjVal? "value"
  let value : ConstantValue ← match ← value.getObjValAs? String "kind" with
    | "zero_sized" => pure ConstantValue.zeroSized
    | "scalar" => do
      let some bits := (← value.getObjValAs? String "bits").toNat? | throw "source MIR scalar bits invalid"
      let size ← value.getObjValAs? Nat "size_bytes"
      unless size > 0 && size ≤ 16 && bits < 2^(8*size) do throw "source MIR scalar bits/width invalid"
      pure (.scalar bits size)
    | "allocation_slice" => do
      pure (.allocationSlice (← allocationRef c (← value.getObjValAs? Nat "allocation"))
        (← value.getObjValAs? Nat "metadata"))
    | "allocation_indirect" => do
      pure (.allocationIndirect (← allocationRef c (← value.getObjValAs? Nat "allocation"))
        (← value.getObjValAs? Nat "offset_bytes"))
    | "allocation_pointer" => do
      let immutable ← value.getObjValAs? Bool "immutable"
      let sharedRef ← value.getObjValAs? Bool "shared_ref"
      unless !immutable || sharedRef do throw "source MIR immutable allocation provenance is not shared"
      pure (.allocationPointer (← allocationRef c (← value.getObjValAs? Nat "allocation"))
        (← value.getObjValAs? Nat "offset_bytes") immutable sharedRef)
    | "value" | "param" => pure (ConstantValue.typeConstant (← constantExpr c value))
    | "unevaluated" => do
      let definition ← definitionRef c (← value.getObjValAs? Nat "definition")
      let promoted ← value.getObjValAs? (Option Nat) "promoted"
      pure (ConstantValue.unevaluated definition (← arguments c (← value.getObjVal? "arguments")) promoted)
    | tag => pure (.unsupported tag)
  return ⟨type,value,← spanKey (← j.getObjVal? "source_span_key"),← optionalNat j "user_type"⟩
private def operand (c : Context) (j : Json) : Except String Operand := do
  match ← j.getObjValAs? String "kind" with
  | "copy" => return .copy (← place c (← j.getObjVal? "place"))
  | "move" => return .move (← place c (← j.getObjVal? "place"))
  | "constant" => return .constant (← constant c j)
  | "runtime_checks" =>
    let tag ← j.getObjValAs? String "check"
    let check : Option MIR.RuntimeChecks := match tag with
      | "ub_checks" => some .UbChecks | "contract_checks" => some .ContractChecks
      | "overflow_checks" => some .OverflowChecks | _ => none
    let some check := check | return .unsupported s!"runtime_checks:{tag}"
    let reference ← typeRef c (← j.getObjValAs? Nat "type")
    let some physical := c.physical | throw "runtime-check bool source universe unavailable"
    let some (.primitive "bool" _) := physical.types[reference]? | throw "runtime-check operand type is not bool"
    return .runtimeChecks check reference

  | tag => pure (.unsupported tag)
private def binary (tag : String) : Operator MIR.BinOp :=
  match tag with
  | "add" => .known .Add | "add_unchecked" => .known .AddUnchecked | "add_with_overflow" => .known .AddWithOverflow
  | "sub" => .known .Sub | "sub_unchecked" => .known .SubUnchecked | "sub_with_overflow" => .known .SubWithOverflow
  | "mul" => .known .Mul | "mul_unchecked" => .known .MulUnchecked | "mul_with_overflow" => .known .MulWithOverflow
  | "div" => .known .Div | "rem" => .known .Rem
  | "bit_xor" => .known .BitXor | "bit_and" => .known .BitAnd | "bit_or" => .known .BitOr
  | "shift_left" => .known .Shl | "shift_left_unchecked" => .known .ShlUnchecked
  | "shift_right" => .known .Shr | "shift_right_unchecked" => .known .ShrUnchecked
  | "equal" => .known .Eq | "less_than" => .known .Lt | "less_equal" => .known .Le
  | "not_equal" => .known .Ne | "greater_equal" => .known .Ge | "greater_than" => .known .Gt
  | "compare" => .known .Cmp | "pointer_offset" => .known .Offset | _ => .unsupported tag
private def rvalue (c : Context) (j : Json) : Except String Rvalue := do
  match ← j.getObjValAs? String "kind" with
  | "use" => return .use (← operand c (← j.getObjVal? "operand")) (← j.getObjValAs? Bool "retag")
  | "ref" =>
    let kind ← j.getObjValAs? String "borrow_kind"
    let borrow := match kind with
      | "shared" => Operator.known MIR.BorrowKind.Shared
      | "mut_default" => .known (.Mut .Default)
      | "mut_two_phase" => .known (.Mut .TwoPhaseBorrow)
      | "mut_closure_capture" => .known (.Mut .ClosureCapture)
      | _ => .unsupported kind
    return .reference (← SourceTypesParser.region (← j.getObjVal? "region")) borrow (← place c (← j.getObjVal? "place"))
  | "raw_ptr" =>
    let kind : Operator MIR.RawPtrKind := match ← j.getObjValAs? String "pointer_kind" with
      | "const" => .known .Const
      | "mut" => .known .Mut
      | "fake_for_ptr_metadata" => .known .FakeForPtrMetadata
      | tag => .unsupported tag
    return .rawPointer kind (← place c (← j.getObjVal? "place"))
  | "binary" =>
    return .binary (binary (← j.getObjValAs? String "operator"))
      (← operand c (← j.getObjVal? "left")) (← operand c (← j.getObjVal? "right"))
  | "unary" =>
    let tag ← j.getObjValAs? String "operator"
    let op : Operator MIR.UnOp := match tag with
      | "not" => .known .Not
      | "negate" => .known .Neg
      | "pointer_metadata" => .known .PtrMetadata
      | _ => .unsupported tag
    return .unary op (← operand c (← j.getObjVal? "operand"))
  | "repeat" => return .repeat (← operand c (← j.getObjVal? "operand")) (← constantExpr c (← j.getObjVal? "length"))
  | "discriminant" => return .discriminant (← place c (← j.getObjVal? "place"))
  | "aggregate_closure" =>
    return .aggregateClosure (← definitionRef c (← j.getObjValAs? Nat "definition"))
      (← arguments c (← j.getObjVal? "arguments")) (← (← j.getObjValAs? (Array Json) "operands").mapM (operand c))
  | "aggregate_adt" =>
    let definition ← definitionRef c (← j.getObjValAs? Nat "definition")
    let variant ← j.getObjValAs? Nat "variant"
    let args ← arguments c (← j.getObjVal? "arguments")
    let userType ← optionalNat j "user_type"
    let activeField ← optionalNat j "active_field"
    let values ← (← j.getObjValAs? (Array Json) "operands").mapM (operand c)
    let some physical := c.physical | throw "Unsupported aggregate ADT declaration capability unavailable"
    let some declared := physical.definitions[definition]? | throw "source aggregate ADT declaration absent"
    let some adt := declared.adt | throw "source aggregate owner is not an ADT"
    let some selected := adt.variants[variant]? | throw "source aggregate ADT variant out of bounds"
    match adt.kind with
    | .unionKind =>
      unless variant == 0 && adt.variants.size == 1 do throw "source union aggregate variant invalid"
      let some field := activeField | throw "source union aggregate active field absent"
      unless field < selected.fields.size && values.size == 1 do throw "source union aggregate field/operand invalid"
    | .structKind | .enumKind =>
      unless activeField.isNone && values.size == selected.fields.size do throw "source ADT aggregate field/operand mismatch"
    return .aggregateAdt definition variant args userType activeField values
  | "aggregate_tuple" => return .aggregateTuple (← (← j.getObjValAs? (Array Json) "operands").mapM (operand c))
  | "aggregate_array" =>
    let element ← typeRef c (← j.getObjValAs? Nat "element_type")
    let values ← (← j.getObjValAs? (Array Json) "operands").mapM (operand c)
    return .aggregateArray element values
  | "pointer_coercion" =>
    let coercion ← j.getObjVal? "coercion"
    let kind : Operator MIR.PointerCoercion ← match ← coercion.getObjValAs? String "kind" with
      | "unsize" => pure (.known .Unsize)
      | "reify_fn_pointer" =>
        match ← coercion.getObjValAs? String "safety" with
        | "safe" => pure (.known (.ReifyFnPointer .Safe))
        | "unsafe" => pure (.known (.ReifyFnPointer .Unsafe))
        | tag => pure (.unsupported ("reify_fn_pointer safety:" ++ tag))
      | tag => pure (.unsupported tag)
    let tag ← j.getObjValAs? String "source"
    let source : Operator MIR.CoercionSource := match tag with
      | "as_cast" => .known .AsCast
      | "implicit" => .known .Implicit
      | _ => .unsupported tag
    return .pointerCoercion kind (← operand c (← j.getObjVal? "operand")) (← typeRef c (← j.getObjValAs? Nat "target")) source
  | "cast" =>
    let kind : Operator MIR.CastKind ← match ← j.getObjValAs? String "cast_kind" with
      | "pointer_expose_provenance" => pure (.known .PointerExposeProvenance)
      | "pointer_with_exposed_provenance" => pure (.known .PointerWithExposedProvenance)
      | "int_to_int" => pure (.known .IntToInt)
      | "float_to_int" => pure (.known .FloatToInt)
      | "float_to_float" => pure (.known .FloatToFloat)
      | "int_to_float" => pure (.known .IntToFloat)
      | "fn_ptr_to_ptr" => pure (.known .FnPtrToPtr)
      | "box_deref_transmute" => pure (.known .BoxDerefTransmute)
      | "subtype" => pure (.known .Subtype)
      | "transmute" => pure (.known .Transmute)
      | "ptr_to_ptr" => pure (.known .PtrToPtr)
      | tag => pure (.unsupported tag)
    return .cast kind (← operand c (← j.getObjVal? "operand")) (← typeRef c (← j.getObjValAs? Nat "target"))
  | tag => pure (.unsupported tag)
private def reason (j : Json) : Except String (Operator MIR.UnwindTerminateReason) := do
  match ← j.getObjValAs? String "kind" with
  | "abi" => pure (.known .Abi) | "in_cleanup" => pure (.known .InCleanup) | tag => pure (.unsupported tag)
private def unwind (c : Context) (j : Json) : Except String Unwind := do
  match ← j.getObjValAs? String "kind" with
  | "Continue" => pure .continueUnwind | "Unreachable" => pure .unreachable
  | "Cleanup" => return .cleanup (← blockRef c (← j.getObjValAs? Nat "target"))
  | "Terminate" => return .terminate (← reason (← j.getObjVal? "reason"))
  | tag => pure (.unsupported tag)
private def callSource (tag : String) : Operator MIR.CallSource :=
  match tag with
  | "normal_call" => .known .Normal | "overloaded_operator" => .known .OverloadedOperator
  | "match_comparison" => .known .MatchCmp | "miscellaneous_desugaring" => .known .Misc
  | "clone_or_use" => .known .Use | _ => .unsupported tag
private def info (c : Context) (j : Json) : Except String Input.SourceMir.SourceInfo := do
  let source ← sourceSpan (← j.getObjVal? "span")
  let scope ← j.getObjValAs? Nat "scope"
  unless scope < c.scopes do throw "source MIR source scope reference out of bounds"
  return ⟨source.identity,scope⟩
private def coroutine (j : Json) : Except String (Operator MIR.CoroutineKind) := do
  match ← j.getObjValAs? String "kind" with
  | "coroutine" =>
    match ← j.getObjValAs? String "movability" with
    | "static" => return .known (.Coroutine .Static)
    | "movable" => return .known (.Coroutine .Movable)
    | tag => return .unsupported tag
  | "desugared" =>
    let tag ← j.getObjValAs? String "desugaring"
    let kind : Option MIR.CoroutineDesugaring := match tag with
      | "async" => some .Async | "gen" => some .Gen | "async_gen" => some .AsyncGen | _ => none
    let some kind := kind | return .unsupported tag
    let tag ← j.getObjValAs? String "source"
    let source : Option MIR.CoroutineSource := match tag with
      | "block" => some .Block | "closure" => some .Closure | "function" => some .Fn | _ => none
    let some source := source | return .unsupported tag
    return .known (.Desugared kind source)
  | tag => return .unsupported tag
private def assertKind (c : Context) (j : Json) : Except String Input.SourceMir.AssertKind := do
  match ← j.getObjValAs? String "kind" with
  | "bounds_check" => return .boundsCheck (← operand c (← j.getObjVal? "length")) (← operand c (← j.getObjVal? "index"))
  | "overflow" =>
    return .overflow (binary (← j.getObjValAs? String "operator"))
      (← operand c (← j.getObjVal? "left")) (← operand c (← j.getObjVal? "right"))
  | "overflow_neg" => return .overflowNeg (← operand c (← j.getObjVal? "operand"))
  | "division_by_zero" => return .divisionByZero (← operand c (← j.getObjVal? "operand"))
  | "remainder_by_zero" => return .remainderByZero (← operand c (← j.getObjVal? "operand"))
  | "resumed_after_return" => return .resumedAfterReturn (← coroutine (← j.getObjVal? "coroutine"))
  | "resumed_after_panic" => return .resumedAfterPanic (← coroutine (← j.getObjVal? "coroutine"))
  | "resumed_after_drop" => return .resumedAfterDrop (← coroutine (← j.getObjVal? "coroutine"))
  | "misaligned_pointer_dereference" =>
    return .misalignedPointerDereference
      (← operand c (← j.getObjVal? "required")) (← operand c (← j.getObjVal? "found"))
  | "null_pointer_dereference" => pure .nullPointerDereference
  | "null_reference_constructed" => pure .nullReferenceConstructed
  | "invalid_enum_construction" => return .invalidEnumConstruction (← operand c (← j.getObjVal? "operand"))
  | tag => pure (.unsupported tag)
def terminator (c : Context) (j : Json) (call : Option Json) : Except String TerminatorKind := do
  match ← j.getObjValAs? String "kind" with
  | "return" => pure .returnValue | "unwind_resume" => pure .resumeUnwind | "unreachable" => pure .unreachable
  | "unwind_terminate" => return .terminateUnwind (← reason (← j.getObjVal? "reason"))
  | "goto" => return .goto (← blockRef c (← j.getObjValAs? Nat "target"))
  | "drop" =>
    let asyncDrop ← (← optionalNat j "async_drop").mapM (blockRef c)
    return .drop (← place c (← j.getObjVal? "place")) (← blockRef c (← j.getObjValAs? Nat "target"))
      (← unwind c (← j.getObjVal? "unwind")) (← j.getObjValAs? Bool "replace") asyncDrop
  | "assert" =>
    return .assert (← operand c (← j.getObjVal? "condition")) (← j.getObjValAs? Bool "expected")
      (← assertKind c (← j.getObjVal? "message")) (← blockRef c (← j.getObjValAs? Nat "target"))
      (← unwind c (← j.getObjVal? "unwind"))
  | "switch_int" =>
    let values ← (← j.getObjValAs? (Array Json) "targets").mapM fun t => do
      let some value := (← t.getObjValAs? String "value").toNat? | throw "source MIR switch bits invalid"
      unless value < 2^128 do throw "source MIR switch bits exceed u128"
      return (value,← blockRef c (← t.getObjValAs? Nat "target"))
    unless values.toList.Pairwise (fun a b => a.1 != b.1) do throw "source MIR duplicate switch value"
    return .switchInt (← operand c (← j.getObjVal? "operand")) values (← blockRef c (← j.getObjValAs? Nat "otherwise"))
  | "call" =>
    let some call := call | throw "source MIR call span evidence unavailable"
    let target ← (← optionalNat j "target").mapM (blockRef c)
    let argumentValues ← j.getObjValAs? (Array Json) "arguments"
    let spans ← call.getObjValAs? (Array Json) "arguments"
    unless argumentValues.size == spans.size do throw "source MIR call argument/span count differs"
    let args ← (argumentValues.zip spans).mapM fun (arg,span) => do
      return SpannedOperand.mk (← operand c arg) (← sourceSpan span).identity
    return .call (← operand c (← j.getObjVal? "function")) args (← place c (← j.getObjVal? "destination"))
      target (← unwind c (← j.getObjVal? "unwind")) (callSource (← j.getObjValAs? String "call_source"))
      (← sourceSpan (← call.getObjVal? "function")).identity
  | tag => pure (.unsupported tag)
/-- Shared instruction parser; initializer syntax has no invented SourceInfo. -/
def statementKind (c : Context) (statement : Json) : Except String StatementKind := do
  match ← statement.getObjValAs? String "kind" with
  | "assign" => pure (StatementKind.assign (← place c (← statement.getObjVal? "place")) (← rvalue c (← statement.getObjVal? "value")))
  | "storage_live" => pure (StatementKind.storageLive (← localRef c (← statement.getObjValAs? Nat "local")))
  | "storage_dead" => pure (StatementKind.storageDead (← localRef c (← statement.getObjValAs? Nat "local")))
  | "place_mention" => pure (StatementKind.placeMention (← place c (← statement.getObjVal? "place")))
  | "nop" => pure .nop
  | tag => pure (.unsupported tag)
private def phase (j : Json) : Except String Phase := do
  let tag ← j.getObjValAs? String "kind"
  if tag == "runtime" then
    match ← j.getObjValAs? String "phase" with
    | "initial" => pure (.known (.Runtime .Initial)) | "post_cleanup" => pure (.known (.Runtime .PostCleanup))
    | "optimized" => pure (.known (.Runtime .Optimized)) | tag => pure (.unsupported ("runtime:" ++ tag))
  else pure (.unsupported tag)

def body (document : Document) (j : Json) (promoted : Option Nat := none) (physical : Option Input.SourceTypes.Material := none) : Except String Body := do
  validateSourceMetadata j
  let defId ← j.getObjValAs? Nat "definition"
  let some definition := document.definitions[defId]? | throw "source MIR owner reference absent"
  let metadata ← j.getObjVal? "source_metadata"
  let scopes ← metadata.getObjValAs? (Array Json) "scopes"
  let localTypes ← j.getObjValAs? (Array Nat) "locals"
  let sourceLocals ← metadata.getObjValAs? (Array Json) "locals"
  let blocks ← j.getObjValAs? (Array Json) "blocks"
  let locations ← metadata.getObjValAs? (Array Json) "blocks"
  let calls ← metadata.getObjValAs? (Array Json) "call_spans"
  let c : Context := ⟨document.types.size,document.definitions.size,localTypes.size,blocks.size,scopes.size,
    (← document.source.getObjValAs? (Array Json) "source_allocations").size,physical⟩
  let argCount ← j.getObjValAs? Nat "argument_count"
  unless !blocks.isEmpty && argCount < localTypes.size do throw "source MIR argument/local/block count invalid"
  let registry ← buildSpanRegistry j
  let mut compilerSpans := registry.compilerSpans
  if let .ok additional := metadata.getObjValAs? (Array Json) "additional_spans" then
    for raw in additional do
      let extra ← sourceSpan raw
      if let some old := compilerSpans[extra.identity]? then
        unless old == extra do throw "source MIR additional span identity conflict"
      else
        unless extra.identity == compilerSpans.size do throw "source MIR additional span identity gap"
        compilerSpans := compilerSpans.push extra
  let spans := compilerSpans.map fun source => {
    identity := source.identity, key := ⟨source.lo,source.hi,source.context,source.parentLocalDefinition⟩,
    isDummy := source.isDummy,file := source.file,startLine := source.startLine,startColumn := source.startColumn,
    endLine := source.endLine,endColumn := source.endColumn : Span }
  let locals ← (localTypes.zip sourceLocals).mapM fun (ty,source) =>
    return Local.mk (← typeRef c ty) (← source.getObjValAs? Bool "mutable") (← info c (← source.getObjVal? "source_info"))
  let typedScopes ← scopes.mapM fun source =>
    return Scope.mk (← sourceSpan (← source.getObjVal? "span")).identity
      (← optionalNat source "parent") (← optionalNat source "inlined_parent")
  let typedBlocks ← (blocks.zip (locations.zip calls)).mapM fun (block,(location,call)) => do
    let statements ← block.getObjValAs? (Array Json) "statements"
    let sources ← location.getObjValAs? (Array Json) "statements"
    let statements ← (statements.zip sources).mapM fun (statement,source) => do
      let kind ← statementKind c statement
      return Statement.mk (← info c source) kind
    return Block.mk (← block.getObjValAs? Bool "cleanup") statements
      ⟨← info c (← location.getObjVal? "terminator"),← terminator c (← block.getObjVal? "terminator") (some call)⟩
  let required ← (← j.getObjValAs? (Array Json) "required_consts").mapM fun entry => do
    unless (← entry.getObjValAs? String "kind") == "constant" do throw "source MIR required entry is not a constant"
    constant c entry
  let backtraces := (← sourceBacktraces j).map fun bt =>
    Backtrace.mk bt.span.identity bt.bytePosition bt.line bt.zeroBasedCharColumn bt.filename
  let spread ← match j.getObjVal? "spread_argument" with
    | .error _ => pure none | .ok value => (← fromJson? value : Option Nat).mapM (localRef c)
  return {
    definition := ⟨← definition.getObjValAs? Nat "crate_index",← definition.getObjValAs? Nat "index"⟩,
    promoted,promotedCount := ← j.getObjValAs? Nat "promoted_count", phase := ← phase (← metadata.getObjVal? "phase"),
    injectionPhase := ← (← metadata.getObjValAs? (Option Json) "injection_phase").mapM phase,
    argumentCount := argCount,spreadArgument := spread,
    bodySpan := (← sourceSpan (← metadata.getObjVal? "span")).identity,
    definitionSpan := (← sourceSpan (← metadata.getObjVal? "definition_span")).identity,
    spans, scopes := typedScopes,backtraces,locals,blocks := typedBlocks,requiredConstants := required}

def material (document : Document) (physical : Option Input.SourceTypes.Material := none) : Except String Input.SourceMir.Material :=
  (do
    let mut bodies ← document.bodies.mapM (fun row => body document row none physical)
    if let .ok closures := document.source.getObjValAs? (Array Json) "closure_templates" then
      for closure in closures do bodies := bodies.push (← body document closure none physical)
    let root ← sourceSpan (← (← document.source.getObjVal? "session").getObjVal? "root_span")
    let rootSpan : Span := {
      identity := root.identity,key := ⟨root.lo,root.hi,root.context,root.parentLocalDefinition⟩,
      isDummy := root.isDummy,file := root.file,startLine := root.startLine,startColumn := root.startColumn,
      endLine := root.endLine,endColumn := root.endColumn }
    return ({rootSpan,bodies} : Input.SourceMir.Material)).mapError fun error => "Invalid typed source MIR: " ++ error

end Miri.Frontend.Foundation.SourceMirParser
