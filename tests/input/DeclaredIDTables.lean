import Miri.Input.Reader.Catalog

open Lean Miri.Input.Reader

private def document (table key : String) (values : Array Nat) : Json :=
  Json.mkObj [("shared_payloads", Json.mkObj [
    ("schema_version",toJson (2 : Nat)), ("nodes", Json.arr #[])]),
    (table,Json.arr (values.map fun id => Json.mkObj [(key,toJson id)]))]

private def must (value : Except String A) : IO A :=
  match value with
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

def main : IO Unit := do
  for (table,key) in [("types","type_id"),("allocations","allocation_id"),("instances","instance_id")] do
    let catalog ← must (Catalog.parse (document table key #[2,0,1]))
    let values ← must (catalog.array (← must (catalog.field catalog.root table "$")) table)
    for (value,index) in values.toList.zipIdx do
      unless (← must (catalog.natural (← must (catalog.field value key table)) table)) == index do
        throw (IO.userError s!"{table} used row order as ID")
    unless !(Catalog.parse (document table key #[0,0])).isOk do
      throw (IO.userError s!"{table} accepted duplicate IDs")
    unless !(Catalog.parse (document table key #[0,2])).isOk do
      throw (IO.userError s!"{table} accepted an out-of-bounds ID")
    let roundTrip ← must (Catalog.parse (← must catalog.input))
    unless roundTrip.root == catalog.root && roundTrip.nodes == catalog.nodes do
      throw (IO.userError s!"{table} indexing is unstable")
  let reference := Json.mkObj [("$lean_miri_shared_ref",toJson (0 : Nat))]
  let shared := Json.mkObj [("schema_version",toJson (2 : Nat)),
    ("nodes",Json.arr #[Json.mkObj [("instance_id",toJson (0 : Nat))]])]
  let input := Json.mkObj [("shared_payloads",shared),("instances",Json.arr #[reference])]
  let catalog ← must (Catalog.parse input)
  let values ← must (catalog.array (← must (catalog.field catalog.root "instances" "$")) "instances")
  unless values == #[reference] do throw (IO.userError "declared-ID indexing expanded shared records")
  IO.println "declared ID tables: PASS (types/allocations/instances; shuffle, duplicates, bounds, shared IDs)"
