import Miri.Memory.KeyedArray

open Miri.Memory

private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def main : IO Unit := do
  let original : KeyedArray Nat (Nat × Nat) Prod.fst :=
    KeyedArray.ofArray Prod.fst #[(2, 10), (1, 20), (2, 30)]
  let same := original.mapValuesChecked fun row => (row.1, row.2 + 1)
  assertTrue (same.toArray == #[(2, 11), (1, 21), (2, 31)])
    "same-key mapping changed source row order or payloads"
  assertTrue (same.find? 2 == some (2, 11) && same.valuesFor 2 == #[(2, 11), (2, 31)])
    "same-key mapping changed first-match or duplicate-order lookup"
  let changed := original.mapValuesChecked fun row =>
    ((if row.1 == 1 then 2 else row.1), row.2 + 5)
  assertTrue (changed.toArray == #[(2, 15), (2, 25), (2, 35)])
    "key-changing mapping changed row order or payloads"
  assertTrue (changed.find? 1 == none && changed.find? 2 == some (2, 15))
    "key-changing mapping retained a stale old key or lost the first new-key row"
  assertTrue (changed.valuesFor 2 == #[(2, 15), (2, 25), (2, 35)])
    "key-changing fallback lost or reordered duplicate rows"
  assertTrue (original.toArray == #[(2, 10), (1, 20), (2, 30)])
    "mapping changed the original value"
  IO.println "KeyedArray checked mapping: PASS"
