import Miri.Input.GenericArgsCodec

open Lean Miri.MIR Miri.Input

private def referenceArgs : String :=
  "[{\"kind\":\"type\",\"value\":17},{\"kind\":\"const\",\"value\":23},{\"kind\":\"lifetime\",\"value\":{\"kind\":\"bound\",\"index_kind\":{\"kind\":\"bound\",\"debruijn_index\":2},\"variable_index\":3,\"bound_kind\":{\"kind\":\"named\",\"def_id\":41}}}]"

private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)

def main : IO Unit := do
  let args ← match (JsonReader.parse referenceArgs >>= GenericArgsCodec.decode) with
    | .ok value => pure value | .error error => throw (IO.userError error)
  check (decide (args = #[.Type 17, .Const 23, .Lifetime (.Bound (.Bound 2) 3 (.Named 41))]))
    "generic references or bound region identity changed"
  let obsolete := JsonReader.parse
    "[{\"kind\":\"const\",\"value\":{\"type_constant_id\":23}}]" >>= GenericArgsCodec.decode
  check (!obsolete.isOk) "obsolete wrapped constant reference accepted"
  IO.println "generic argument IDs and binder identity preserved; obsolete wrapper rejected"
