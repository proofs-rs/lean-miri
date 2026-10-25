import Miri.Memory.KeyedArray

open Miri.Memory

private def keyOf (row : Nat × Nat) : Nat := row.1

private structure CollisionKey where
  value : Nat
  deriving BEq

private instance : Hashable CollisionKey where
  hash _ := 0

private def check (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def checkRows (rows : Array (Nat × Nat)) : IO Unit := do
  let indexed := KeyedArray.ofArray keyOf rows
  check (indexed.toArray == rows) "source row order changed"
  check (indexed.toPairs == rows.map (fun row => (row.1, row))) "key/row alignment changed"
  for key in #[0, 1, 2, 3, 4, 9] do
    let matching := rows.filter (fun row => row.1 == key)
    check (indexed.find? key == matching[0]?) s!"first matching row changed for {key}"
    check (indexed.valuesFor key == matching) s!"duplicate row order changed for {key}"
    check (indexed.contains key == (!matching.isEmpty)) s!"membership changed for {key}"
    for threshold in #[0, 10, 20, 30, 40] do
      let predicate := fun row : Nat × Nat => row.2 >= threshold
      check (indexed.any? key predicate == matching.any predicate)
        s!"later matching row predicate changed for {key}/{threshold}"

def main : IO Unit := do
  let rows := #[(3, 10), (2, 20), (3, 30), (1, 40), (3, 11)]
  checkRows rows
  let indexed := KeyedArray.ofArray keyOf rows
  let pushed := indexed.push (3, 99)
  checkRows pushed.toArray
  check (pushed.find? 3 == some (3, 10)) "append displaced first duplicate"
  let filtered := pushed.filter (fun _ row => row.2 >= 20)
  checkRows filtered.toArray
  check (filtered.find? 3 == some (3, 30)) "filter did not reindex first duplicate"
  let mapped := pushed.mapValues (fun row => (row.1 + 1, row.2))
  checkRows mapped.toArray
  check (mapped.find? 4 == some (4, 10)) "mapped key was not rebuilt"
  let colliding := KeyedArray.ofArray (fun row : CollisionKey × Nat => row.1)
    #[(⟨1⟩, 10), (⟨2⟩, 20), (⟨1⟩, 30)]
  check (colliding.find? ⟨1⟩ == some (⟨1⟩, 10)) "colliding first key changed"
  check (colliding.find? ⟨2⟩ == some (⟨2⟩, 20)) "colliding other key changed"
  check (colliding.valuesFor ⟨1⟩ == #[(⟨1⟩, 10), (⟨1⟩, 30)])
    "colliding duplicate order changed"
  IO.println "KeyedArray indexed lookup, duplicate order, append, filter and rekey: PASS"
