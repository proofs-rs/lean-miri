import Miri.Input.JsonTraversalCache

open Lean Miri.Input

private def document (nodes : Array Json) (fields : List (String × Json)) : Json :=
  Json.mkObj (("shared_payloads", Json.mkObj [("schema_version", toJson (2 : Nat)),
    ("nodes", .arr nodes)]) :: fields)
private def reference (id : Nat) : Json := Json.mkObj [("$lean_miri_shared_ref", toJson id)]
private def check (input : Json) : IO Unit := do
  let .ok original := SharedPayloads.resolveGraph input | throw (IO.userError "bad fixture")
  let .ok (resolved,node) := JsonTraversalCache.resolve input | throw (IO.userError "cached resolution failed")
  unless resolved.root == original.root && node.value == original.root && node.audit do
    throw (IO.userError "cached hash/value differs from original resolver")
  let .ok (_,slow) := JsonTraversalCache.resolve input false | throw (IO.userError "slow resolution failed")
  unless slow.key.digest == hash original.root do throw (IO.userError "fallback hash differs")

private def malformedObject : Json := Id.run do
  let leaf : Std.DTreeMap.Internal.Impl String (fun _ : String => Json) := .leaf
  let duplicate := Std.DTreeMap.Internal.Impl.inner 1 "status" (.str "x") leaf leaf
  let root := Std.DTreeMap.Internal.Impl.inner 2 "status" (.str "x") leaf duplicate
  return .obj ⟨⟨root⟩⟩

def main : IO Unit := do
  let flagged := document #[Json.mkObj [("type_id", toJson (7 : Nat))],
      .arr #[reference 0], Json.mkObj [("locals", .arr #[])]] [("root", reference 1)]
  let addFlags (flags : Json) : Json := match flagged with
    | .obj fields => .obj (fields.insert "shared_payloads" (Json.mkObj [
        ("schema_version", toJson (2 : Nat)), ("nodes", .arr #[
          Json.mkObj [("type_id", toJson (7 : Nat))], .arr #[reference 0],
          Json.mkObj [("locals", .arr #[])]]), ("scan_flags", flags)]))
    | other => other
  let good := addFlags (toJson (#[1, 1, 2] : Array Nat))
  check good
  for enabled in [true, false] do
    match JsonTraversalCache.resolve good enabled with
    | .ok _ => pure ()
    | .error error => throw (IO.userError s!"valid prepared summaries rejected: {error}")
    for bad in [toJson (#[0, 1, 2] : Array Nat), toJson (#[1, 15, 2] : Array Nat),
        toJson (#[1] : Array Nat), toJson (#[1, 16, 2] : Array Nat), .null] do
      match JsonTraversalCache.resolve (addFlags bad) enabled with
      | .error error => unless error.contains "scan_flags" do
          throw (IO.userError s!"wrong prepared-summary error: {error}")
      | .ok _ => throw (IO.userError "forged scan summaries accepted")
  for capacity in [0, 1, 7, 64] do
    let mut dense := JsonTraversalCache.IdentitySet.empty capacity
    let mut reference : Std.HashSet JsonTraversalCache.IdentityKey := {}
    let keys := (Array.range 80).map (fun n => .node ((n * 17) % 83))
    let raw := (JsonTraversalCache.Node.uncached (.str "raw fallback")).identity
    let keys := keys.push raw
    for key in keys do
      dense := dense.insert key
      reference := reference.insert key
      for query in keys do
        unless dense.contains query == reference.contains query do
          throw (IO.userError "dense identity membership differs from exact reference set")
  for n in [:40] do
    let leaf := Json.mkObj [("n",toJson n), ("s",.str s!"value-{n}"), ("flag",toJson (n % 2 == 0)), ("null",.null)]
    let nodes := #[leaf, leaf, .arr #[reference 0, reference 1],
      Json.mkObj [("left",reference 2), ("right",reference 2)]]
    check (document nodes [("root",reference 3), ("inline",leaf)])
  let leaf := Json.mkObj [("status", .str "unsupported")]
  let input := document #[leaf, leaf] [("a",reference 0), ("b",reference 0),
    ("c",reference 1), ("d",leaf)]
  let .ok (_,root) := JsonTraversalCache.resolve input | throw (IO.userError "ID fixture failed")
  let a := root.field "a" leaf
  let b := root.field "b" leaf
  let c := root.field "c" leaf
  let d := root.field "d" leaf
  unless a.identity == b.identity && !(a.identity == c.identity) &&
      !(a.identity == d.identity) && a.key == c.key && a.key == d.key &&
      a.shouldMemo && !d.shouldMemo do
    throw (IO.userError "reference identity or distinct equal-node IDs were lost")
  let bad := document #[malformedObject] [("root",reference 0)]
  let .ok (_,node) := JsonTraversalCache.resolve bad | throw (IO.userError "malformed raw resolver failed")
  match node with
  | .uncached _ => pure ()
  | _ => throw (IO.userError "noncanonical raw object enabled caching")
  let forward := document #[reference 1, .null] [("root", reference 0)]
  match SharedPayloads.resolveGraph forward, JsonTraversalCache.resolve forward with
  | .error a, .error b => unless a == b do throw (IO.userError "transport error changed")
  | _, _ => throw (IO.userError "invalid graph accepted")
  IO.println "cached hashes, duplicates, shared/inline values, fallback and transport errors: PASS"

#print axioms Miri.Input.JsonTraversalCache.Key.beq_eq
#print axioms Miri.Input.JsonTraversalCache.uncached_hash_eq
