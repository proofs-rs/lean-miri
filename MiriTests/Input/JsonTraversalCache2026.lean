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
