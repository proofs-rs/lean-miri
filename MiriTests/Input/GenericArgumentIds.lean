import Miri.Input.GenericArgsCodec

open Lean Miri.MIR Miri.Input

private def referenceArgs : Json := .arr #[
  Json.mkObj [("kind", .str "type"), ("value", toJson (17 : Nat))],
  Json.mkObj [("kind", .str "const"), ("value", toJson (23 : Nat))],
  Json.mkObj [("kind", .str "lifetime"), ("value", Json.mkObj [
    ("kind", .str "bound"),
    ("index_kind", Json.mkObj [("kind", .str "bound"), ("debruijn_index", toJson (2 : Nat))]),
    ("variable_index", toJson (3 : Nat)),
    ("bound_kind", Json.mkObj [("kind", .str "named"), ("def_id", toJson (41 : Nat))])])]]

private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)

def main : IO Unit := do
  let args ← match GenericArgsCodec.decode referenceArgs with
    | .ok value => pure value | .error error => throw (IO.userError error)
  check (decide (args = #[.Type 17, .Const 23, .Lifetime (.Bound (.Bound 2) 3 (.Named 41))]))
    "generic references or bound region identity changed"
  let obsolete := GenericArgsCodec.decode (.arr #[Json.mkObj [
    ("kind", .str "const"), ("value", Json.mkObj [("type_constant_id", toJson (23 : Nat))])]])
  check (!obsolete.isOk) "obsolete wrapped constant reference accepted"
  IO.println "generic argument IDs and binder identity preserved; obsolete wrapper rejected"
