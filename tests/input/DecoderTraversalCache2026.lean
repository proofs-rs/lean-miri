import Miri.Input.Decoder

open Lean Miri.Input

private def compare (name text : String) : IO Unit := do
  match decodeRuntimeJson text, decodeRuntimeJsonReference text with
  | .error a, .error b =>
    unless a == b do throw (IO.userError s!"{name}: first diagnostic changed: {a} / {b}")
  | .ok a, .ok b =>
    unless a.executionInput.isSome == b.executionInput.isSome &&
      a.blockingObligations == b.blockingObligations &&
      a.document.obligations == b.document.obligations &&
      a.document.functionAbis.map (·.payload) == b.document.functionAbis.map (·.payload) &&
      a.document.bodies.map (·.payload) == b.document.bodies.map (·.payload) do
        throw (IO.userError s!"{name}: readiness, ordered obligations, ABI or body sequence changed")
  | _, _ => throw (IO.userError s!"{name}: decoder result class changed")

private def set (j : Json) (key : String) (value : Json) : Json :=
  match j with
  | .obj fields => Json.mkObj ((key,value) :: fields.toList.filter (fun e => e.1 != key))
  | _ => Json.mkObj [(key,value)]

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected decoder-id-inputs")
  for name in ["genuine-mir-features", "genuine-fresh", "valid-permuted-dense",
    "duplicate-and-range-first", "out-of-range-type-id", "negative-type-id",
    "malformed-table-type-id", "dangling-type", "dangling-allocation", "dangling-instance",
    "malformed-type-reference", "malformed-allocation-reference", "malformed-instance-reference",
    "nested-debug-payload-skips-references", "empty-allocations", "empty-instances"] do
    compare name (← IO.FS.readFile s!"{directory}/{name}.json")
  let base ← IO.FS.readFile s!"{directory}/genuine-fresh.json"
  let .ok document := Json.parse base | throw (IO.userError "fixture parse")
  let bad := Json.mkObj [("kind",.str "Cast"), ("vtable_allocation", Json.mkObj [
      ("kind",.str "dynamic_vtable_upcast"),("status",.str "supported")])]
  compare "early-vtable-error" (set (set document "a_first" bad) "z_later" bad).compress
  let malformedAbi := Json.mkObj [("fn_abi",Json.mkObj [("status",.str "supported")])]
  compare "first-abi-error" (set (set document "a_first" malformedAbi) "z_later" malformedAbi).compress
  IO.println "cached/uncached decoder diagnostics and ordered ABI/body results: PASS"
