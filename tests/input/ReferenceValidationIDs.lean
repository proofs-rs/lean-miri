import Miri.Input.Reader.ReferenceValidation

open Lean Miri.Input.Reader

private def ref (id : Nat) : Json := Json.mkObj [("$lean_miri_shared_ref", toJson id)]

private def wrap (nodes : Array Json) (root : Json) : Json :=
  Json.mkObj [("shared_payloads", Json.mkObj [
    ("schema_version", toJson (2 : Nat)), ("nodes", .arr nodes)]), ("value", root)]

private def check (nodes : Array Json) (root : Json) (expected : Bool) : IO Unit := do
  let catalog ← match Catalog.parse (wrap nodes root) with
    | .ok value => pure value
    | .error reason => throw (IO.userError reason)
  unless (catalog.validateReferences 2 3 4).isOk == expected do
    throw (IO.userError "transport DAG reference validation disagreed with expected bounds")

def main : IO Unit := do
  -- Reuse a shared subtree containing both a direct type reference and a
  -- nested allocation reference. The validator follows IDs at each edge.
  let nodes := #[Json.mkObj [("type_id", toJson (1 : Nat))],
    Json.mkObj [("allocation_id", toJson (2 : Nat))], .arr #[ref 0, ref 1]]
  check nodes (.arr #[ref 2, ref 2]) true
  check #[Json.mkObj [("type_id", toJson (2 : Nat))]] (ref 0) false
  check #[Json.mkObj [("allocation_id", toJson (3 : Nat))]] (ref 0) false
  check #[Json.mkObj [("instance_id", toJson (4 : Nat)), ("kind", toJson "item")]] (ref 0) false
  check #[toJson "debug_payload", Json.mkObj [("status", ref 0),
      ("value", Json.mkObj [("type_id", toJson (99 : Nat))])]] (ref 1) true
  check #[] (Json.mkObj [("type_id", toJson (99 : Nat)), ("debug", .null)]) true
  IO.println "transport DAG reference bounds: PASS"
