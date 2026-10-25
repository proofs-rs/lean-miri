import Lean
import Miri.Input.JsonTraversalCache

/-! Diagnostic for structural hashing of shared JSON DAGs. This does not change
or bypass a decoder check. Each level retains two references to the same child;
the current Json hash recursively visits both edges without a node memo. -/
open Lean

def main : IO Unit := do
  let opts := (({} : Lean.Options).setBool `profiler true).set `profiler.threshold (0 : Nat)
  for depth in [12, 16, 20, 22] do
    let mut value := Json.str "shared-leaf"
    for _ in [:depth] do
      value := Json.arr #[value, value]
    let digest := Lean.profileit s!"json_shared_hash.depth_{depth}" opts (fun _ => hash value)
    let mut nodes := #[Json.str "shared-leaf"]
    for index in [:depth] do
      let reference := Json.mkObj [("$lean_miri_shared_ref", toJson index)]
      nodes := nodes.push (.arr #[reference,reference])
    let document := Json.mkObj [
      ("shared_payloads",Json.mkObj [("schema_version",toJson (2 : Nat)),("nodes",.arr nodes)]),
      ("value",Json.mkObj [("$lean_miri_shared_ref",toJson depth)])]
    let result := Lean.profileit s!"json_cached_build_and_hash.depth_{depth}" opts fun _ => do
      let (_,root) ← Miri.Input.JsonTraversalCache.resolve document
      let child := root.field "value" .null
      pure (hash child.key, root.key.digest, root.value)
    let .ok (cached,rootHash,rootValue) := result | throw (IO.userError "cached graph failed")
    unless cached == digest && rootHash == hash rootValue do
      throw (IO.userError "cached digest differs")
    IO.println s!"depth={depth}; constructed_nodes={depth + 1}; recursive_hash_visits={2^(depth+1)-1}; digest={digest}"
