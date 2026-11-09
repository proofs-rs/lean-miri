import Miri.Input.DecoderValues
import Miri.Input.GenericArgsCodec

namespace Miri.Input.TypeConstCodec
open Lean Miri.MIR DecoderValues JsonReader

private structure TreeFields where
  kind : Option String := none
  size : Option Nat := none
  bits : Option String := none
  elements : Option (Array Nat) := none

private def valueTree (path : String) : Parser ValTree := do
  let v ← object ({} : TreeFields) fun v key => do
    match key with
    | "kind" => return {v with kind := some (← string)}
    | "size_bytes" => return {v with size := some (← natural)}
    | "bits_unsigned" => return {v with bits := some (← string)}
    | "elements" => return {v with elements := some (← array natural)}
    | _ => skipValue; return v
  match ← required v.kind "kind" with
  | "leaf" =>
    if v.elements.isSome then fail s!"{path}: leaf valtree carries branch elements"
    let size ← required v.size "size_bytes"
    let bitsText ← required v.bits "bits_unsigned"
    let some bits := bitsText.toNat? | fail s!"{path}: invalid valtree bits"
    unless size > 0 && size ≤ 16 && bits < 2 ^ (size * 8) do fail s!"{path}: invalid valtree scalar width"
    return ⟨#[.Leaf bits size], 0⟩
  | "branch" =>
    if v.size.isSome || v.bits.isSome then fail s!"{path}: branch valtree carries scalar fields"
    return ⟨#[.Branch (← required v.elements "elements")], 0⟩
  | tag => fail s!"{path}: unknown valtree kind {tag}"

private structure Fields where
  kind : Option String := none
  aliasKind : Option String := none
  rigidity : Option String := none
  definition : Option Nat := none
  args : Option (Array GenericArg) := none
  ty : Option Nat := none
  value : Option ValTree := none
  expressionKind : Option String := none
  operator : Option (Option String) := none
  arguments : Option (Array GenericArg) := none

/-- Parse concrete constant-pool data; references remain numeric IDs. -/
def decode (path : String) : Parser TypeConst := do
  let v ← object ({} : Fields) fun v key => do
    match key with
    | "kind" => return {v with kind := some (← string)}
    | "alias_kind" => return {v with aliasKind := some (← string)}
    | "rigidity" => return {v with rigidity := some (← string)}
    | "def_id" => return {v with definition := some (← natural)}
    | "generic_args" => return {v with args := some (← GenericArgsCodec.decode)}
    | "type" => return {v with ty := some (← natural)}
    | "value" => return {v with value := some (← valueTree (path ++ ".value"))}
    | "expression_kind" => return {v with expressionKind := some (← string)}
    | "operator" => return {v with operator := some (← nullable string)}
    | "arguments" => return {v with arguments := some (← GenericArgsCodec.decode)}
    | _ => skipValue; return v
  match ← required v.kind "kind" with
  | "alias" =>
    if v.ty.isSome || v.value.isSome || v.expressionKind.isSome || v.operator.isSome || v.arguments.isSome then
      fail s!"{path}: alias constant carries incompatible payload fields"
    let kind ← match ← required v.aliasKind "alias_kind" with
      | "projection" => pure ConstAliasKind.Projection
      | "inherent_self" => pure .InherentSelf
      | "inherent_impl" => pure .InherentImpl
      | "free" => pure .Free
      | "anonymous" => pure .Anon
      | tag => fail s!"{path}: unknown const alias kind {tag}"
    let rigid ← match ← required v.rigidity "rigidity" with
      | "rigid" => pure true
      | "not_rigid" => pure false
      | tag => fail s!"{path}: unknown const rigidity {tag}"
    return .Alias rigid kind (← required v.definition "def_id") (← required v.args "generic_args")
  | "value" =>
    if v.aliasKind.isSome || v.rigidity.isSome || v.definition.isSome || v.args.isSome ||
        v.expressionKind.isSome || v.operator.isSome || v.arguments.isSome then
      fail s!"{path}: value constant carries incompatible payload fields"
    return .Value (← required v.ty "type") (← required v.value "value")
  | "expression" =>
    if v.aliasKind.isSome || v.rigidity.isSome || v.definition.isSome || v.args.isSome || v.ty.isSome || v.value.isSome then
      fail s!"{path}: expression constant carries incompatible payload fields"
    let kind ← match ← required v.expressionKind "expression_kind" with
      | "binary_operator" =>
        let operator ← required v.operator.join "operator"
        let some operation := binOpFromExportTag operator | fail s!"{path}: unknown binary operator {operator}"
        pure (.Binop operation)
      | "unary_operator" =>
        let operator ← required v.operator.join "operator"
        let some operation := unOpFromExportTag operator | fail s!"{path}: unknown unary operator {operator}"
        pure (.UnOp operation)
      | "function_call" =>
        if v.operator.join.isSome then fail s!"{path}: function-call expression carries an operator"
        pure .FunctionCall
      | "cast" =>
        match ← required v.operator.join "operator" with
        | "as" => pure (.Cast .As)
        | "use" => pure (.Cast .Use)
        | tag => fail s!"{path}: unknown const cast {tag}"
      | tag => fail s!"{path}: unknown const expression {tag}"
    return .Expr kind (← required v.arguments "arguments")
  | tag => fail s!"{path}: unknown type constant kind {tag}"

end Miri.Input.TypeConstCodec
