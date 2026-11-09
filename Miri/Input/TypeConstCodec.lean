import Miri.Input.DecoderValues
import Miri.Input.GenericArgsCodec

namespace Miri.Input.TypeConstCodec
open Lean Miri.MIR DecoderValues

private def valueTree (value : JsonReader.Slice) (path : String) : Except String ValTree := do
  match ← fieldString value "kind" path with
  | "leaf" =>
    let size ← fieldNat value "size_bytes" path
    let bitsText ← fieldString value "bits_unsigned" path
    let some bits := bitsText.toNat? | throw s!"{path}: invalid valtree bits"
    unless size > 0 && size ≤ 16 && bits < 2 ^ (size * 8) do throw s!"{path}: invalid valtree scalar width"
    pure ⟨#[.Leaf bits size], 0⟩
  | "branch" =>
    let children ← (← arrayField value "elements" path).mapM JsonReader.Slice.natural
    pure ⟨#[.Branch children], 0⟩
  | tag => throw s!"{path}: unknown valtree kind {tag}"

def decode (value : JsonReader.Slice) (path : String) : Except String TypeConst := do
  match ← fieldString value "kind" path with
  | "alias" =>
    let aliasKind ← fieldString value "alias_kind" path
    let kind ← match aliasKind with
      | "projection" => pure ConstAliasKind.Projection
      | "inherent_self" => pure .InherentSelf
      | "inherent_impl" => pure .InherentImpl
      | "free" => pure .Free
      | "anonymous" => pure .Anon
      | tag => throw s!"{path}: unknown const alias kind {tag}"
    let rigidity ← fieldString value "rigidity" path
    let rigid ← match rigidity with
      | "rigid" => pure true
      | "not_rigid" => pure false
      | tag => throw s!"{path}: unknown const rigidity {tag}"
    return .Alias rigid kind (← fieldNat value "def_id" path)
      (← GenericArgsCodec.decode (← field value "generic_args" path))
  | "value" =>
    return .Value (← fieldNat value "type" path)
      (← valueTree (← field value "value" path) (joinPath path "value"))
  | "expression" =>
    let expressionKind ← fieldString value "expression_kind" path
    let kind ← match expressionKind with
      | "binary_operator" =>
        let operator ← fieldString value "operator" path
        let some operation := binOpFromExportTag operator | throw s!"{path}: unknown binary operator {operator}"
        pure (.Binop operation)
      | "unary_operator" =>
        let operator ← fieldString value "operator" path
        let some operation := unOpFromExportTag operator | throw s!"{path}: unknown unary operator {operator}"
        pure (.UnOp operation)
      | "function_call" => pure .FunctionCall
      | "cast" =>
        match ← fieldString value "operator" path with
        | "as" => pure (.Cast .As)
        | "use" => pure (.Cast .Use)
        | tag => throw s!"{path}: unknown const cast {tag}"
      | tag => throw s!"{path}: unknown const expression {tag}"
    return .Expr kind (← GenericArgsCodec.decode (← field value "arguments" path))
  | tag => throw s!"{path}: unknown type constant kind {tag}"

end Miri.Input.TypeConstCodec
