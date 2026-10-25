import Miri.Input.SharedPayloads

open Lean
open Miri.Input.SharedPayloads

private def fail (message : String) : IO α := throw (IO.userError message)

private def parse (source : String) : IO Json :=
  match Json.parse source with
  | .ok value => pure value
  | .error error => fail s!"invalid test JSON: {error}"

private def expectJson (actual expected : Json) (label : String) : IO Unit :=
  if actual == expected then pure () else fail s!"{label}: got {actual}, expected {expected}"

def main : IO UInt32 := do
  let input ← parse "{\"shared_payloads\":{\"schema_version\":2,\"nodes\":[{\"payload\":[1,2]},[\"head\",{\"$lean_miri_shared_ref\":0},\"middle\",{\"$lean_miri_shared_ref\":0},\"tail\"],[\"plain\",9]]},\"root_array\":[\"left\",{\"$lean_miri_shared_ref\":1},\"right\"]}"
  let graph ← match resolveGraph input with
    | .ok graph => pure graph
    | .error error => fail s!"valid array graph rejected: {error}"
  let payload ← parse "{\"payload\":[1,2]}"
  let expectedArray ← parse "[\"head\",{\"payload\":[1,2]},\"middle\",{\"payload\":[1,2]},\"tail\"]"
  let expectedPlain ← parse "[\"plain\",9]"
  let expectedRoot ← parse "[\"left\",[\"head\",{\"payload\":[1,2]},\"middle\",{\"payload\":[1,2]},\"tail\"],\"right\"]"
  let [nodeZero, nodeOne, nodeTwo] := graph.nodes.toList
    | fail "array graph did not retain exactly three nodes"
  expectJson nodeZero payload "node zero"
  expectJson nodeOne expectedArray "multiple array replacements with untouched prefix/suffix"
  expectJson nodeTwo expectedPlain "array with no references"
  let rootArray ← match graph.root.getObjVal? "root_array" with
    | .ok value => pure value
    | .error _ => fail "root array missing after resolution"
  expectJson rootArray expectedRoot "root array with nested array reference"
  IO.println "SharedPayloadArrayRegression: passed"
  return 0
