import Miri.Input.Decoder

open Miri.Input

private def accepted : List String := ["valid-dense", "nested-debug-payload-skips-references"]

private def rejected : List String := [
  "missing-type-shape-kind", "missing-type-layout-size", "permuted-type-rows",
  "duplicate-and-range-first", "out-of-range-type-id", "negative-type-id",
  "malformed-table-type-id", "dangling-type", "dangling-allocation", "dangling-instance",
  "malformed-type-reference", "malformed-allocation-reference", "malformed-instance-reference",
  "empty-allocations", "empty-instances"]

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected decoder ID case directory")
  for name in accepted do
    match decodeJson (← IO.FS.readFile s!"{directory}/{name}.json") with
    | .ok _ => IO.println s!"PASS {name}: accepted"
    | .error error => throw (IO.userError s!"valid control {name} rejected: {error}")
  for name in rejected do
    match decodeJson (← IO.FS.readFile s!"{directory}/{name}.json") with
    | .error error => IO.println s!"PASS {name}: {error}"
    | .ok _ => throw (IO.userError s!"invalid table/reference accepted: {name}")
