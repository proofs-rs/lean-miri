import Miri.Input.SharedPayloads

open Lean
open Miri.Input.SharedPayloads

private def fail (message : String) : IO α := throw (IO.userError message)

private def check (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else fail message

private def parse (source : String) : Json :=
  match Json.parse source with
  | .ok value => value
  | .error error => panic! s!"bad test JSON: {error}"

private def succeeds (source : String) : Except String ResolvedGraph :=
  resolveGraph (parse source)

private def rejects (source : String) : Bool :=
  match succeeds source with
  | .error _ => true
  | .ok _ => false

private partial def markerCount : Json → Nat
  | .arr values => values.foldl (fun count value => count + markerCount value) 0
  | .obj fields => fields.toList.foldl (fun count (key, value) =>
      count + (if key == "$lean_miri_shared_ref" then 1 else 0) + markerCount value) 0
  | _ => 0

private def checkFixture (path : String) : IO Unit := do
  let source ← IO.FS.readFile path
  let input ← match Json.parse source with
    | .ok value => pure value
    | .error error => fail s!"{path}: invalid fixture JSON: {error}"
  let graph ← match resolveGraph input with
    | .ok value => pure value
    | .error error => fail s!"{path}: graph rejected: {error}"
  check (!graph.nodes.isEmpty) s!"{path}: fixture contains no shared graph nodes"
  check (graph.nodeResolutionCount == graph.nodes.size)
    s!"{path}: node resolution count does not match catalog size"
  check (markerCount input > 0) s!"{path}: fixture contains no shared references"

def main (args : List String) : IO UInt32 := do
  let graph := parse "{\"root_a\":{\"$lean_miri_shared_ref\":0},\"root_b\":{\"$lean_miri_shared_ref\":1},\"root_c\":{\"$lean_miri_shared_ref\":2},\"shared_payloads\":{\"schema_version\":2,\"nodes\":[{\"span\":{\"start\":4,\"end\":9}},{\"layout\":{\"inner\":{\"$lean_miri_shared_ref\":0}}},{\"$lean_miri_shared_ref\":1}]}}"
  let resolved ← match resolveGraph graph with
    | .ok value => pure value
    | .error error => fail s!"valid graph rejected: {error}"
  check (resolved.nodeResolutionCount == 3) "resolver did not process each catalog node once"
  check (resolved.nodes.size == 3) "resolved graph lost a catalog node"
  let rootA ← match resolved.root.getObjVal? "root_a" with
    | .ok value => pure value
    | .error _ => fail "resolved root_a is missing"
  let rootB ← match resolved.root.getObjVal? "root_b" with
    | .ok value => pure value
    | .error _ => fail "resolved root_b is missing"
  let rootC ← match resolved.root.getObjVal? "root_c" with
    | .ok value => pure value
    | .error _ => fail "resolved root_c is missing"
  check (rootA == resolved.nodes[0]!) "root reference did not reuse node zero value"
  check (rootB == resolved.nodes[1]!) "root reference did not reuse node one value"
  check (rootC == resolved.nodes[1]!) "transitive graph reference was not resolved"
  check (match resolved.root.getObjVal? "shared_payloads" with | .error _ => true | .ok _ => false)
    "transport catalog leaked into business root"
  check (rejects "{\"schema\":\"x\"}") "missing catalog was accepted"
  check (rejects "{\"shared_payloads\":{\"nodes\":[]}}") "missing graph version was accepted"
  check (rejects "{\"shared_payloads\":{\"schema_version\":1,\"nodes\":[]}}") "legacy version was accepted"
  check (rejects "{\"shared_payloads\":{\"schema_version\":2,\"nodes\":[{\"$lean_miri_shared_ref\":0}]}}")
    "self-cycle was accepted"
  check (rejects "{\"shared_payloads\":{\"schema_version\":2,\"nodes\":[{\"$lean_miri_shared_ref\":1}]}}")
    "forward reference was accepted"
  check (rejects "{\"root\":{\"$lean_miri_shared_ref\":4},\"shared_payloads\":{\"schema_version\":2,\"nodes\":[]}}")
    "out-of-range root reference was accepted"
  check (rejects "{\"root\":{\"$lean_miri_shared_ref\":-1},\"shared_payloads\":{\"schema_version\":2,\"nodes\":[]}}")
    "negative reference was accepted"
  check (rejects "{\"root\":{\"$lean_miri_shared_ref\":{\"index\":0}},\"shared_payloads\":{\"schema_version\":2,\"nodes\":[]}}")
    "non-numeric reference was accepted"
  check (rejects "{\"$lean_miri_shared_ref\":0,\"shared_payloads\":{\"schema_version\":2,\"nodes\":[{}]}}")
    "root-level shared reference was accepted"
  check (rejects "{\"root\":{\"$lean_miri_shared_ref\":0,\"extra\":true},\"shared_payloads\":{\"schema_version\":2,\"nodes\":[{}]}}")
    "reference marker with extra fields was accepted"
  check (rejects "{\"shared_payloads\":{\"schema_version\":2,\"nodes\":[{}, {\"unused\":{\"$lean_miri_shared_ref\":2}}, {}]}}")
    "forward reference in an unused node was accepted"
  for path in args do
    checkFixture path
  IO.println "SharedGraphTests: passed"
  return 0
