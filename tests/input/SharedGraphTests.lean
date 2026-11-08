import Miri.Input.SharedPayloads

open Lean Miri.Input Miri.Input.SharedPayloads

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def obj := Json.mkObj
private def set (source : Json) (key : String) (value : Json) : Json :=
  match source with
  | .obj fields => .obj (fields.insert key value)
  | _ => obj [(key, value)]
private def table (catalog : Json) (kind : SemanticTables.Kind) (nodes : Array Json) : Json :=
  set catalog kind.table (.arr nodes)
private def emptyCatalog : Json := obj (("schema_version", toJson (1 : Nat)) ::
  SemanticTables.kinds.toList.map (fun kind => (kind.table, .arr #[])))
private def document (catalog : Json) : Json := obj [("semantic_tables", catalog)]
private def rejects (input : Json) : Bool := (resolveGraph input).toOption.isNone

private def checkFixture (path : String) : IO Unit := do
  let input ← must (Json.parse (← IO.FS.readFile path))
  let graph ← must (resolveGraph input)
  check (!graph.nodes.isEmpty) s!"{path}: fixture contains no semantic nodes"
  check (graph.nodeResolutionCount == 0 && graph.root == input)
    s!"{path}: numeric references were expanded or root data changed"
  let total := SemanticTables.kinds.foldl (fun total kind =>
    total + (graph.semanticTables.nodes kind).size) 0
  check (graph.nodes.size == total) s!"{path}: flattened semantic-node view lost entries"

def main (args : List String) : IO UInt32 := do
  let catalog := table (table emptyCatalog .region #[obj [("kind", .str "erased")]])
    .genericArgs #[.arr #[obj [("kind", .str "lifetime"), ("value", toJson (0 : Nat))]]]
  let source := set (set (document catalog) "generic_args" (toJson (0 : Nat))) "region" (toJson (0 : Nat))
  let resolved ← must (resolveGraph source)
  check (resolved.nodeResolutionCount == 0 && resolved.nodes.size == 2)
    "numeric catalog was expanded or lost nodes"
  check (resolved.root == source) "decoder rewrote input numeric references"
  let region ← must (resolved.semanticTables.lookup .region (toJson (0 : Nat)) "$.region")
  let argsNode ← must (resolved.semanticTables.lookup .genericArgs (toJson (0 : Nat)) "$.generic_args")
  check (region != argsNode) "equal IDs in independent semantic kinds collided"
  check (rejects (obj [])) "missing catalog was accepted"
  check (rejects (document (set emptyCatalog "schema_version" .null))) "missing catalog version was accepted"
  check (rejects (document (set emptyCatalog "schema_version" (toJson (2 : Nat))))) "unknown catalog version was accepted"
  let selfCycle := table emptyCatalog .genericArgs #[obj [("generic_args", toJson (0 : Nat))]]
  check (rejects (document selfCycle)) "self cycle was accepted"
  let crossCycle := table (table emptyCatalog .genericArgs #[obj [("region", toJson (0 : Nat))]])
    .region #[obj [("generic_args", toJson (0 : Nat))]]
  check (rejects (document crossCycle)) "cross-kind cycle was accepted"
  check (rejects (set (document catalog) "region" (toJson (4 : Nat)))) "dangling root reference was accepted"
  check (rejects (set (document catalog) "region" (toJson (-1 : Int)))) "negative reference was accepted"
  check (rejects (set (document catalog) "region" (.str "0"))) "nonnumeric reference was accepted"
  let unusedDangling := table catalog .genericArgs #[obj [("region", toJson (9 : Nat))]]
  check (rejects (document unusedDangling)) "dangling reference in an unused semantic node was accepted"
  let wrapper := obj [("type_id", toJson (0 : Nat))]
  check (rejects (set (document catalog) "obsolete" wrapper)) "object-wrapped numeric reference was accepted"
  let marker := obj [("$lean_miri_shared_ref", toJson (0 : Nat)), ("extra", .bool true)]
  check (rejects (set (document catalog) "obsolete" marker)) "obsolete generic marker with extra fields was accepted"
  check (rejects (set (document catalog) "shared_payloads" (obj []))) "obsolete graph catalog was accepted"
  for path in args do checkFixture path
  IO.println "SharedGraphTests: schema-4 numeric catalogs passed"
  return 0
