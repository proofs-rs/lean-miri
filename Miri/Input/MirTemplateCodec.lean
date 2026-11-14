import Miri.Input.MirTemplate
import Miri.Input.GenericMaterialCodec

namespace Miri.Input.MirTemplateCodec
open Lean MirTemplate
private def field (j : Json) (key : String) : Except String Json := j.getObjVal? key
private def nat (j : Json) (key : String) : Except String Nat := do (← field j key).getNat?
private def text (j : Json) (key : String) : Except String String := do (← field j key).getStr?
private def array (j : Json) (key : String) : Except String (Array Json) := do (← field j key).getArr?
private def optionalNat (j : Json) : Except String (Option Nat) :=
  match j with | .null => pure none | _ => some <$> j.getNat?
private def source (j : Json) : Except String Miri.MIR.SourceInfo := do
  pure ⟨⟨← nat j "span"⟩,← nat j "scope"⟩
private def sourcePlace (j : Json) : Except String SourcePlace := do
  let projection ← (← array j "projection").mapM fun value => do
    match ← text value "kind" with
    | "deref" => pure Projection.deref
    | "field" => return .field (← nat value "index") ⟨← nat value "type"⟩
    | "index" => .index <$> nat value "local"
    | "constant_index" => return .constantIndex (← nat value "offset") (← nat value "min_length") (← (← field value "from_end").getBool?)
    | "subslice" => return .subslice (← nat value "from") (← nat value "to") (← (← field value "from_end").getBool?)
    | "downcast" =>
      let name ← match ← field value "name" with
        | .null => pure none | value => some <$> value.getStr?
      return .downcast name (← nat value "variant")
    | _ => throw "unsupported MIR source projection"
  pure ⟨← nat j "local",projection⟩
private def clearedAnnotation (j : Json) : Except String Nat := do
  let value ← field j "user_type"
  let keys := (← value.getObj?).toArray.map (·.1)
  unless keys.size == 3 && keys.all (#["index","table_state","entries"].contains ·) do
    throw "annotated source operand requires complete cleared-table provenance"
  unless (← text value "table_state") == "cleared_post_borrowck" &&
      (← array value "entries").isEmpty do
    throw "source annotation table was not cleared post borrowck"
  let index ← nat value "index"
  unless index < 2^32 do throw "raw source user-type index is not u32"
  pure index
private def sourceOperand (j : Json) : Except String SourceOperand := do
  match ← text j "kind" with
  | "copy" => .copy <$> sourcePlace (← field j "place")
  | "move" => .move <$> sourcePlace (← field j "place")
  | "scalar" =>
    let bits ← text j "bits"
    let some bits := bits.toNat? | throw "invalid MIR source scalar decimal"
    return .scalar ⟨← nat j "type"⟩ ⟨← nat j "span"⟩ bits (← nat j "bytes")
  | "zero_sized" => return .zeroSized ⟨← nat j "type"⟩ ⟨← nat j "span"⟩
  | "annotated_scalar" =>
    let bits ← text j "bits"
    let some bits := bits.toNat? | throw "invalid MIR source scalar decimal"
    return .annotatedScalar ⟨← nat j "type"⟩ ⟨← nat j "span"⟩ bits (← nat j "bytes") (← clearedAnnotation j)
  | "annotated_zero_sized" => return .annotatedZeroSized ⟨← nat j "type"⟩ ⟨← nat j "span"⟩ (← clearedAnnotation j)
  | "unevaluated" =>
    let keys := (← j.getObj?).toArray.map (·.1)
    unless keys.size == 7 && keys.all (#["kind","type","span","definition","arguments","promoted","user_type"].contains ·) do
      throw "raw source Unevaluated field set differs; no evaluated fallback is permitted"
    let arguments ← (← array j "arguments").mapM (GenericMaterialCodec.readTerm 1024)
    let userType ← match ← field j "user_type" with
      | .null => pure none
      | _ => some <$> clearedAnnotation j
    pure (.unevaluated ⟨← nat j "type"⟩ ⟨← nat j "span"⟩
      (← GenericMaterialCodec.readDefinition (← field j "definition")) arguments
      (← optionalNat (← field j "promoted")) userType)
  | _ => throw "unsupported MIR source operand"
private def sourceRvalue (j : Json) : Except String SourceRvalue := do
  match ← text j "kind" with
  | "use" =>
    let retag ← match ← text j "retag" with
      | "yes" => pure Miri.MIR.WithRetag.Yes | "no" => pure .No
      | _ => throw "unknown MIR source retag"
    return .use (← sourceOperand (← field j "operand")) retag
  | "cast" =>
    let kind ← match ← text j "cast" with
      | "int_to_int" => pure Miri.MIR.CastKind.IntToInt
      | "float_to_int" => pure .FloatToInt | "float_to_float" => pure .FloatToFloat
      | "int_to_float" => pure .IntToFloat | "ptr_to_ptr" => pure .PtrToPtr
      | "fn_ptr_to_ptr" => pure .FnPtrToPtr | "transmute" => pure .Transmute
      | "pointer_expose_provenance" => pure .PointerExposeProvenance
      | "pointer_with_exposed_provenance" => pure .PointerWithExposedProvenance
      | _ => throw "source cast outside supported source grammar"
    return .cast kind (← sourceOperand (← field j "operand")) ⟨← nat j "target"⟩
  | "reference" =>
    unless (← text j "region") == "erased" do throw "source Ref requires explicit erased region"
    let borrow ← match ← text j "borrow" with
      | "shared" => pure Miri.MIR.BorrowKind.Shared
      | "mut_default" => pure (.Mut .Default) | "mut_two_phase" => pure (.Mut .TwoPhaseBorrow)
      | "mut_closure_capture" => pure (.Mut .ClosureCapture)
      | "fake_shallow" => pure (.Fake .Shallow) | "fake_deep" => pure (.Fake .Deep)
      | _ => throw "source borrow outside supported source grammar"
    return .reference borrow (← sourcePlace (← field j "place"))
  | "raw_pointer" =>
    let kind ← match ← text j "pointer" with
      | "const" => pure Miri.MIR.RawPtrKind.Const | "mut" => pure .Mut
      | "fake_for_metadata" => pure .FakeForPtrMetadata
      | _ => throw "source raw pointer outside supported source grammar"
    return .rawPointer kind (← sourcePlace (← field j "place"))
  | "discriminant" => .discriminant <$> sourcePlace (← field j "place")
  | "adt" => return .adt ⟨← nat j "type"⟩ (← nat j "variant") (← (← array j "operands").mapM sourceOperand)
  | "tuple" => .tuple <$> (← array j "operands").mapM sourceOperand
  | _ => throw "unsupported MIR source rvalue"
private def sourceUnwind (j : Json) : Except String Miri.MIR.UnwindAction := do
  match ← text j "kind" with
  | "unreachable" => pure .Unreachable
  | "continue" => pure .Continue
  | "cleanup" => .Cleanup <$> nat j "target"
  | _ => throw "unsupported MIR source unwind"
private def coroutineKind (j : Json) : Except String Miri.MIR.CoroutineKind := do
  match ← text j "kind" with
  | "coroutine" =>
    match ← text j "movability" with
    | "static" => pure (.Coroutine .Static)
    | "movable" => pure (.Coroutine .Movable)
    | _ => throw "invalid coroutine movability"
  | "desugared" =>
    let kind ← match ← text j "desugaring" with
      | "async" => pure Miri.MIR.CoroutineDesugaring.Async
      | "gen" => pure .Gen | "async_gen" => pure .AsyncGen
      | _ => throw "invalid coroutine desugaring"
    let source ← match ← text j "source" with
      | "block" => pure Miri.MIR.CoroutineSource.Block
      | "closure" => pure .Closure | "function" => pure .Fn
      | _ => throw "invalid coroutine source"
    pure (.Desugared kind source)
  | _ => throw "invalid coroutine kind"
private def operand (j : Json) : Except String MirTemplate.Operand := do
  match ← text j "kind" with
  | "copy" => .copy <$> nat j "local"
  | "move" => .move <$> nat j "local"
  | _ => throw "unsupported copy-template operand"
private def rvalue (j : Json) : Except String MirTemplate.Rvalue := do
  match ← text j "kind" with
  | "use" =>
    let retag ← match ← text j "retag" with
      | "yes" => pure Miri.MIR.WithRetag.Yes | "no" => pure .No
      | _ => throw "unknown copy-template retag"
    pure (.use (← operand (← field j "operand")) retag)
  | "tuple" => .tuple <$> ((← array j "operands").mapM operand)
  | "array" => return .array ⟨← nat j "element"⟩ (← (← array j "operands").mapM operand)
  | _ => throw "unsupported copy-template rvalue"
private def statement (j : Json) : Except String MirTemplate.Statement := do
  let value ← field j "kind"
  let kind ← match ← text value "kind" with
    | "source_assign" => pure (MirTemplate.StatementKind.sourceAssign
        (← sourcePlace (← field value "place")) (← sourceRvalue (← field value "value")))
    | "source_place_mention" => .sourcePlaceMention <$> sourcePlace (← field value "place")
    | "set_discriminant" => pure (.setDiscriminant (← sourcePlace (← field value "place")) (← nat value "variant"))
    | "assign" => do
      let destination ← nat value "destination"
      let expression ← rvalue (← field value "value")
      pure (MirTemplate.StatementKind.assign destination expression)
    | "storage_live" => .storageLive <$> nat value "local"
    | "storage_dead" => .storageDead <$> nat value "local"
    | "place_mention" => .placeMention <$> nat value "local"
    | "nop" => pure .nop
    | _ => throw "unsupported copy-template statement"
  pure ⟨← source (← field j "source"),kind⟩
private def terminator (j : Json) : Except String MirTemplate.Terminator := do
  let value ← field j "kind"
  let kind ← match ← text value "kind" with
    | "source_call" =>
      let arguments ← (← array value "arguments").mapM fun argument => do
        pure (⟨⟨← nat argument "span"⟩,← sourceOperand (← field argument "operand")⟩ : SourceCallArgument)
      pure (MirTemplate.TerminatorKind.sourceCall ⟨← nat value "function"⟩ ⟨← nat value "constant_span"⟩
        arguments (← sourcePlace (← field value "place")) (← optionalNat (← field value "target"))
        (← sourceUnwind (← field value "unwind")) ⟨← nat value "function_span"⟩)
    | "source_switch" =>
      let cases ← (← array value "cases").mapM fun entry => do
        let bits ← text entry "value"
        let some bits := bits.toNat? | throw "invalid MIR source switch decimal"
        pure (Miri.MIR.SwitchTarget.Case bits (← nat entry "target"))
      pure (MirTemplate.TerminatorKind.sourceSwitch (← sourceOperand (← field value "operand")) ⟨cases,← nat value "otherwise"⟩)
    | "assert_resume" =>
      let kind ← coroutineKind (← field value "coroutine")
      let message ← match ← text value "message" with
        | "return" => pure (Miri.MIR.AssertKind.ResumedAfterReturn kind)
        | "panic" => pure (.ResumedAfterPanic kind)
        | "drop" => pure (.ResumedAfterDrop kind)
        | _ => throw "invalid coroutine resume assertion"
      pure (.assertResume (← sourceOperand (← field value "operand"))
        (← (← field value "expected").getBool?) message (← nat value "target") (← sourceUnwind (← field value "unwind")))
    | "source_drop" => pure (.sourceDrop (← sourcePlace (← field value "place"))
        (← nat value "target") (← sourceUnwind (← field value "unwind"))
        (← (← field value "replace").getBool?) (← optionalNat (← field value "async_drop")))
    | "unwind_resume" => pure .unwindResume
    | "return" => pure MirTemplate.TerminatorKind.return
    | "unreachable" => pure .unreachable
    | "goto" => .goto <$> nat value "target"
    | "call" => do
      let args ← (← array value "arguments").mapM fun argument => do
        let argumentSpan ← nat argument "span"
        let value ← operand (← field argument "operand")
        pure (⟨⟨argumentSpan⟩,value⟩ : MirTemplate.CallArgument)
      let unwind ← match ← text value "unwind" with
        | "unreachable" => pure Miri.MIR.UnwindAction.Unreachable
        | _ => throw "ordinary source call requires unreachable unwind"
      let callSource ← match ← text value "call_source" with
        | "normal" => pure Miri.MIR.CallSource.Normal
        | _ => throw "ordinary source call requires normal source"
      pure (.call ⟨← nat value "function_type"⟩ ⟨← nat value "constant_span"⟩ args
        (← nat value "destination") (← optionalNat (← field value "target")) unwind
        callSource ⟨← nat value "function_span"⟩)
    | "switch" => do
      let cases ← (← array value "cases").mapM fun entry => do
        pure (Miri.MIR.SwitchTarget.Case (← nat entry "value") (← nat entry "target"))
      pure (.switchInt (← operand (← field value "operand")) ⟨cases,← nat value "otherwise"⟩)
    | _ => throw "unsupported copy-template terminator"
  pure ⟨← source (← field j "source"),kind⟩
private def block (j : Json) : Except String MirTemplate.Block := do
  pure ⟨← (← array j "statements").mapM statement,← terminator (← field j "terminator"),
    ← (← field j "cleanup").getBool?⟩

def readTemplate (j : Json) : Except String MirTemplate.Template := do
  let parameters ← (← array j "parameters").mapM GenericMaterialCodec.readSort
  let types ← (← array j "types").mapM (GenericMaterialCodec.readTerm 16384)
  let body ← field j "skeleton"
  unless (← text body "phase") == "runtime_optimized" do throw "copy template requires optimized runtime phase"
  let locals ← (← array body "locals").mapM fun value => MirTemplate.TypeSlot.mk <$> value.getNat?
  let blocks ← (← array body "blocks").mapM block
  let result : MirTemplate.Template := ⟨parameters,types,⟨.Runtime .Optimized,← nat body "argument_count",
    ← optionalNat (← field body "spread_argument"),locals,blocks⟩⟩
  MirTemplate.validateStructure result
  pure result

def decode (text : String) : Except String MirTemplate.Template :=
  Json.parse text >>= readTemplate
end Miri.Input.MirTemplateCodec
