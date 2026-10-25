import Miri.Memory.MemoryState

open Miri.Memory

private def pairKey (row : Nat × Nat) : Nat := row.1

private def sample : KeyedArray Nat (Nat × Nat) pairKey :=
  KeyedArray.ofArray pairKey #[(1, 10), (1, 20), (2, 30)]

private structure CollisionKey where
  value : Nat
  deriving BEq

private instance : Hashable CollisionKey where
  hash _ := 0

private def collisionKey (row : CollisionKey × Nat) : CollisionKey := row.1

private def wrongIssuedProfile : KeyedArray UInt64 AllocId (fun (_ : AllocId) => 0) :=
  KeyedArray.empty (fun (_ : AllocId) => 0)

/- The public MemoryState constructor now fixes each table's extraction profile
in its argument type. A caller cannot inject a table indexed by a different
function, even through the constructor. -/
/- error: Application type mismatch -/
#guard_msgs (error, substring := true) in
#check (MemoryState.mk (Prov := Unit) (Extra := Unit) (MachineKind := Unit)
  1 false wrongIssuedProfile #[] #[]
  (KeyedArray.empty (fun (global : GlobalAllocation) => global.allocId.value))
  (KeyedArray.empty (@Prod.fst Nat AllocId))
  (KeyedArray.empty (@Prod.fst UInt64 Nat))
  (KeyedArray.empty AllocId.value)
  (KeyedArray.empty AllocId.value)
  #[] false false 1 false
  (KeyedArray.empty (fun (pair : AllocId × UInt64) => pair.1.value))
  (KeyedArray.empty (@Prod.fst UInt64 AllocId)) #[] false)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def main : IO Unit := do
  check (sample.keyOf (1, 2) == 1)
    "keyOf compatibility accessor changed extractor behavior"
  check (sample.toArray == #[(1, 10), (1, 20), (2, 30)])
    "toArray changed source order or duplicate rows"
  check (sample.toPairs == #[(1, (1, 10)), (1, (1, 20)), (2, (2, 30))])
    "toPairs changed source order or indexed keys"
  check (sample.contains 1 && !(sample.contains 3))
    "contains changed key membership"
  check (!sample.isEmpty && sample.size == 3)
    "isEmpty or size changed row counting"
  check (sample.find? 1 == some (1, 10))
    "find? changed first-row duplicate lookup"
  check (sample.find? 3 == none)
    "find? changed missing-key behavior"
  check (sample.valuesFor 1 == #[(1, 10), (1, 20)])
    "valuesFor changed duplicate row order"
  check (sample.any? 1 (fun row => row.2 == 20))
    "any? stopped checking later duplicate rows"
  check (!(sample.any? 1 (fun row => row.2 == 99)))
    "any? accepted a missing duplicate payload"
  check ((sample.push (1, 40)).toArray == #[(1, 10), (1, 20), (2, 30), (1, 40)])
    "push changed source order"
  check ((sample.push (1, 40)).find? 1 == some (1, 10))
    "push changed first-row duplicate lookup"
  check ((sample.filter (fun key _ => key != 1)).toArray == #[(2, 30)])
    "filter changed row order or keys"
  check ((sample.mapValues (fun row => (row.1 + 10, row.2))).find? 11 == some (11, 10))
    "mapValues failed to rebuild an index after key changes"
  check ((sample.mapValuesChecked (fun row => (row.1, row.2 + 1))).find? 1 == some (1, 11))
    "mapValuesChecked changed results for a key-preserving map"
  check ((sample.mapValuesChecked (fun row => (row.1 + 10, row.2))).find? 11 == some (11, 10))
    "mapValuesChecked failed to rebuild an index after key changes"
  let merged := KeyedArray.ofArray (@Prod.fst Nat Nat) #[(2, 10), (1, 20), (2, 30)]
      |>.mapValuesChecked fun row => ((if row.1 == 1 then 2 else row.1), row.2 + 5)
  check (merged.toArray == #[(2, 15), (2, 25), (2, 35)])
    "key-changing mapValuesChecked changed row order or payloads"
  check (merged.find? 1 == none && merged.find? 2 == some (2, 15) &&
      merged.valuesFor 2 == #[(2, 15), (2, 25), (2, 35)])
    "key-changing mapValuesChecked did not preserve first-match and duplicate order"
  let colliding := KeyedArray.ofArray collisionKey
      #[(⟨1⟩, 10), (⟨2⟩, 20), (⟨1⟩, 30)]
  check (colliding.find? ⟨1⟩ == some (⟨1⟩, 10) &&
      colliding.find? ⟨2⟩ == some (⟨2⟩, 20) &&
      colliding.valuesFor ⟨1⟩ == #[(⟨1⟩, 10), (⟨1⟩, 30)])
    "hash collisions changed key equality or duplicate ordering"
  IO.println "KeyedArray profile typing and ordered duplicate semantics passed"
