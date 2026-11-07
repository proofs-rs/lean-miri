import Miri.Input.Reader.BodyValidation
import Miri.Input.Reader.ReferenceValidation

open Lean Miri.Input.Reader

private def ref (id : Nat) : Json := Json.mkObj [("$lean_miri_shared_ref", toJson id)]

private def wrap (nodes : Array Json) (root : Json) : Json :=
  Json.mkObj [("shared_payloads", Json.mkObj [
    ("schema_version", toJson (2 : Nat)), ("nodes", .arr nodes)]), ("value", root)]

private def body (locals : Nat) (statement terminator : Json) : Json :=
  Json.mkObj [("locals", .arr ((List.range locals).toArray.map fun localId =>
      Json.mkObj [("local", toJson localId)])),
    ("basic_blocks", .arr #[Json.mkObj [("block", toJson (0 : Nat)),
      ("statements", .arr #[Json.mkObj [("kind", statement)]]),
      ("terminator", Json.mkObj [("kind", terminator)])]])]

private def check (nodes : Array Json) (root : Json) (expected : Bool) : IO Unit := do
  let catalog ← match Catalog.parse (wrap nodes root) with
    | .ok value => pure value
    | .error reason => throw (IO.userError reason)
  unless catalog.validateBodies.isOk == expected do
    throw (IO.userError "transport DAG body validation disagreed with expected bounds")

private def must (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

def main (args : List String) : IO Unit := do
  let placeLocal : Nat → Json := fun id => Json.mkObj [("local", toJson (id : Nat))]
  let ret := Json.mkObj [("variant", toJson "Return")]
  let jump := fun target => Json.mkObj [("variant", toJson "Goto"), ("target", target)]
  check #[placeLocal 0, ret] (body 1 (ref 0) (ref 1)) true
  check #[placeLocal 1, ret] (body 1 (ref 0) (ref 1)) false
  check #[toJson (0 : Nat)] (body 1 .null (jump (ref 0))) true
  check #[toJson (1 : Nat)] (body 1 .null (jump (ref 0))) false
  -- Shared MIR must be checked separately for each body's local domain.
  check #[placeLocal 1, ret] (.arr #[body 2 (ref 0) (ref 1), body 1 (ref 0) (ref 1)]) false
  check #[] (body 0 .null ret) false
  check #[] (Json.mkObj [("locals", .arr #[])]) false
  check #[] (Json.mkObj [("status", toJson "debug_payload"), ("locals", .arr #[])]) true
  -- Null and target references are inspected before optional-edge checking.
  let call := Json.mkObj [("variant", toJson "Call"), ("target", ref 0),
    ("unwind", Json.mkObj [("kind", toJson "Unreachable")])]
  check #[.null] (body 1 .null call) true
  for path in args do
    let catalog ← must (Catalog.parse (← must (Json.parse (← IO.FS.readFile path))))
    let count := fun name => (catalog.field catalog.root name "$" >>=
      fun values => catalog.array values name).map Array.size
    must (catalog.validateReferences (← must (count "types"))
      (← must (count "allocations")) (← must (count "instances")))
    must catalog.validateBodies
  IO.println "transport DAG body bounds: PASS"
