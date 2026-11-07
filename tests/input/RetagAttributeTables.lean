import Miri.Input.Reader.RetagQueries

open Lean Miri.Input

private def must (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)
private def ref (id : Nat) : Json := Json.mkObj [("$lean_miri_shared_ref", toJson id)]
private def key (id : Nat) : Json :=
  Json.mkObj [("crate", toJson (0 : Nat)), ("index", toJson id)]
private def row (definition status value : Json) : Json :=
  Json.mkObj [("definition", definition), ("status", status), ("rustc_no_writable", value)]
private def read (nodes : Array Json) (rows : Json) :
    Except String (RetagAttributeTable × Reader.MIRReader.State) := do
  let catalog ← Reader.Catalog.parse (Json.mkObj [("compiler_retag_queries",rows),
    ("shared_payloads", Json.mkObj [("schema_version",toJson (2 : Nat)),("nodes",.arr nodes)])])
  let (result,state) ← (Reader.RetagQueryReader.read catalog).run
    (Reader.MIRReader.initial catalog.nodes.size {definitions := #[⟨0,99⟩]})
  return (← result,state)

def main : IO Unit := do
  let nodes := #[key 7,toJson "supported",toJson true,
    row (ref 0) (ref 1) (ref 2)]
  let (table,state) ← must (read nodes (.arr #[ref 3]))
  unless state.compiler.definitions == #[⟨0,99⟩,⟨0,7⟩] &&
      table.entries[0]?.map (·.2) == some (.error "exact compiler retag frame attribute query absent") &&
      table.entries[1]? == some (⟨0,7⟩,.ok true) do
    throw (IO.userError "retag canonical definition order or shared value changed")
  let rows : Json := .arr #[row (key 7) (toJson "supported") (toJson true),
    row (key 8) (toJson "unsupported") .null,
    row (key 7) (toJson "supported") (toJson false)]
  let (table,_) ← must (read #[] rows)
  unless table.entries[1]?.map (·.2) == some (.error "duplicate compiler retag definition query") &&
      table.entries[2]?.map (·.2) == some (.error "compiler rustc_no_writable attribute query unavailable") &&
      table.absent == .error "duplicate compiler retag definition query" do
    throw (IO.userError "retag ordered duplicate/query failure changed")
  let malformed : Json := .arr #[row (Json.mkObj [("crate",toJson (0 : Nat))])
    (toJson "supported") (toJson true)]
  let (table,_) ← must (read #[] malformed)
  unless !table.absent.isOk && table.entries.all (fun entry => !entry.2.isOk) do
    throw (IO.userError "malformed retag source key accepted")
  IO.println "retag attribute tables: PASS"
