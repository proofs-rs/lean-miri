import Miri.Input.TypeConstCodec

open Lean Miri.Input Miri.MIR

private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)

private def parse (text : String) : IO TypeConst := do
  TypeConstCodec.decode (← must (JsonReader.parse text)) "$constant" |> must

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def main : IO Unit := do
  let expression ← parse "{\"kind\":\"expression\",\"expression_kind\":\"function_call\",\"arguments\":[{\"kind\":\"const\",\"value\":0},{\"kind\":\"const\",\"value\":42}]}"
  check (decide (expression = .Expr .FunctionCall #[.Const 0, .Const 42]))
    "recursive and forward const IDs were expanded or rewritten"
  let alias ← parse "{\"kind\":\"alias\",\"rigidity\":\"rigid\",\"alias_kind\":\"free\",\"def_id\":7,\"generic_args\":[{\"kind\":\"type\",\"value\":1},{\"kind\":\"const\",\"value\":2},{\"kind\":\"lifetime\",\"value\":{\"kind\":\"static\"}}]}"
  check (decide (alias = .Alias true .Free 7 #[.Type 1, .Const 2, .Lifetime .Static]))
    "alias lost its definition identity or owned generic arguments"
  let first ← parse "{\"kind\":\"value\",\"type\":1,\"value\":{\"kind\":\"leaf\",\"bits_unsigned\":\"7\",\"size_bytes\":1}}"
  let second ← parse "{\"kind\":\"value\",\"type\":2,\"value\":{\"kind\":\"leaf\",\"bits_unsigned\":\"7\",\"size_bytes\":1}}"
  check (decide (first ≠ second)) "equal scalar bits erased constant type identity"
  for text in #[
    "{\"kind\":\"value\",\"type\":1,\"value\":{\"kind\":\"leaf\",\"bits_unsigned\":\"256\",\"size_bytes\":1}}",
    "{\"kind\":\"value\",\"type\":1,\"value\":{\"kind\":\"leaf\",\"bits_unsigned\":\"0\",\"size_bytes\":0}}",
    "{\"kind\":\"value\",\"type\":1,\"value\":{\"kind\":\"leaf\",\"bits_unsigned\":\"0\",\"size_bytes\":17}}"] do
    let json ← must (JsonReader.parse text)
    check (!(TypeConstCodec.decode json "$constant").isOk) "invalid scalar width accepted"
  IO.println "type constants retain recursive IDs, alias identity and local arguments; scalar widths checked"
