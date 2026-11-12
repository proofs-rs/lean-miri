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
