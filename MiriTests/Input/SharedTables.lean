import Miri.Input.Reader.SourceSpan
import Miri.Input.Reader.Producer

open Lean Miri.Input.Reader Miri.MIR

private def reference (id : Nat) : Json :=
  Json.mkObj [("$lean_miri_shared_ref", toJson id)]

private def document (nodes : Array Json) (root : Json) : Json :=
  Json.mkObj [("shared_payloads", Json.mkObj [("schema_version", toJson (2 : Nat)),
    ("nodes", .arr nodes)]), ("root", root)]

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def main : IO Unit := do
  let nodes := #[.str "value", .arr #[reference 0, reference 0]]
  let .ok catalog := Catalog.parse (document nodes (reference 1))
    | throw (IO.userError "valid catalog rejected")
  require (catalog.nodes == nodes) "catalog changed shared nodes"
  let .ok root := catalog.root.getObjVal? "root"
    | throw (IO.userError "root missing")
  require (root == reference 1) "catalog expanded the root"
  let .ok children := catalog.array root "$.root"
    | throw (IO.userError "shared array lookup failed")
  require (children == #[reference 0, reference 0]) "array lookup expanded its children"
  let table : SharedTable String := Array.replicate nodes.size none
  let .ok (first, table) := catalog.readEntry table Json.getStr? (reference 0) "first"
    | throw (IO.userError "string construction failed")
  require (first == 0 && (table.lookup first).toOption == some "value") "shared ID lost"
  let .ok (second, table) := catalog.readEntry table (fun _ => .error "decoded twice")
      (reference 0) "second"
    | throw (IO.userError "shared value decoded more than once")
  require (second == first && (table.lookup second).toOption == some "value") "cached reference changed"
  let .ok (inlineValue, table) := catalog.readEntry table Json.getStr? (.str "inline") "inline"
    | throw (IO.userError "inline value rejected")
  require (inlineValue == nodes.size && (table.lookup inlineValue).toOption == some "inline") "inline entry did not get a new table slot"
  require (match table.lookup 1 with | .error 1 => true | _ => false)
    "missing typed entry silently accepted"
  require (match table.lookup 8 with | .error 8 => true | _ => false)
    "out-of-range typed entry silently accepted"
  for input in #[document #[] (reference 0),
      document #[.arr #[reference 0]] (reference 0),
      document #[.arr #[reference 1], .str "later"] (reference 0),
      document #[reference 0] .null,
      document #[] (Json.mkObj [("$lean_miri_shared_ref", toJson (0 : Nat)), ("extra", .null)])] do
    require (match Catalog.parse input with | .error _ => true | .ok _ => false) "invalid reference accepted"
  let diagnostic := fun id => Json.mkObj [("status", .str "debug_payload"),
    ("rustc_debug", reference id)]
  let sourcePosition := fun column => Json.mkObj [("line", toJson (1 : Nat)),
    ("column", toJson (column : Nat))]
  let span := Json.mkObj [("lo", toJson (3 : Nat)), ("hi", toJson (8 : Nat)),
    ("start", sourcePosition 2), ("end", sourcePosition 7),
    ("ctxt", reference 1), ("file", reference 3)]
  let .ok spans := Catalog.parse (document #[.str "context", diagnostic 0,
      .str "src.rs", diagnostic 2, span] (reference 4))
    | throw (IO.userError "span catalog rejected")
  let .ok (spanRef, spanTable) := spans.readSourceSpan
      (Array.replicate spans.nodes.size none) (reference 4) "span"
    | throw (IO.userError "shared span construction failed")
  require (spanRef == 4) "span ID lost during construction"
  let .ok decodedSpan := spanTable.lookup spanRef
    | throw (IO.userError "constructed span absent from table")
  require (decodedSpan.context == "context" && decodedSpan.file == "src.rs" &&
      decodedSpan.lo == 3 && decodedSpan.hi == 8 && decodedSpan.start.column == 2 &&
      decodedSpan.end.column == 7) "semantic span fields changed"
  let producer := Json.mkObj [("miri_commit", reference 0), ("rustc_commit", reference 1),
    ("rustc_version", reference 2), ("target_triple", reference 3)]
  let .ok metadata := Catalog.parse (Json.mkObj [
      ("shared_payloads", Json.mkObj [("schema_version", toJson (2 : Nat)),
        ("nodes", .arr #[.str "miri", .str "rustc", .str "version", .str "target", producer])]),
      ("producer", reference 4)])
    | throw (IO.userError "producer catalog rejected")
  let .ok decodedProducer := metadata.producer
    | throw (IO.userError "shared producer construction failed")
  require (decodedProducer.miriCommit == "miri" && decodedProducer.rustcCommit == "rustc" &&
      decodedProducer.rustcVersion == "version" && decodedProducer.targetTriple == "target")
    "producer semantic fields changed"
  IO.println "shared tables: PASS"

#print axioms Miri.MIR.SharedTable.lookup_some
