import Miri.Input.Decoder

open Lean Miri.Input

private def compare (name text : String) : IO Unit := do
  match decodeRuntimeJson text, decodeRuntimeJsonReference text with
  | .error a, .error b =>
    unless a == b do throw (IO.userError s!"{name}: first diagnostic changed: {a} / {b}")
  | .ok a, .ok b =>
    unless a.document.functionAbis.map (·.payload) == b.document.functionAbis.map (·.payload) &&
      a.document.bodies.map (·.payload) == b.document.bodies.map (·.payload) do
        throw (IO.userError s!"{name}: accepted ABI or body sequence changed")
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
  let base ← IO.FS.readFile s!"{directory}/valid-permuted-dense.json"
  let .ok document := Json.parse base | throw (IO.userError "fixture parse")
  let bad := Json.mkObj [("kind",.str "Cast"), ("vtable_allocation", Json.mkObj [
      ("kind",.str "dynamic_vtable_upcast")])]
  compare "early-vtable-error" (set (set document "a_first" bad) "z_later" bad).compress
  let malformedAbi := Json.mkObj [("fn_abi",Json.mkObj [])]
  compare "first-abi-error" (set (set document "a_first" malformedAbi) "z_later" malformedAbi).compress
  -- Cached and uncached readers reject malformed numeric edges in their
  -- physical semantic node before any executable input exists.
  let huge : Nat := 999999999
  let issue := Json.arr #[Json.mkObj [("kind", .str "lifetime"), ("value", toJson huge)]]
  let .ok catalog := document.getObjVal? "semantic_tables" | throw (IO.userError "missing catalog")
  let .ok nodes := (catalog.getObjVal? "generic_args").bind Json.getArr? | throw (IO.userError "missing nodes")
  let reference := Json.mkObj [("generic_args", toJson nodes.size)]
  let withNode := set document "semantic_tables" (set catalog "generic_args" (.arr (nodes.push issue)))
  let contexts := Json.mkObj [("plain", reference), ("nested", reference),
    ("array", .arr #[reference, reference])]
  let repeated := set (set withNode "synthetic_a" contexts) "synthetic_z.%[" contexts
  compare "semantic-runtime-contexts-and-rebased-paths" repeated.compress
  match decodeRuntimeJson repeated.compress with
  | .error message =>
    unless message.startsWith s!"$.semantic_tables.generic_args[{nodes.size}][0].value:" do
      throw (IO.userError s!"invalid numeric reference diagnostic changed: {message}")
  | .ok _ => throw (IO.userError "failed numeric payload was accepted")
  IO.println "cached/uncached decoder diagnostics and ordered ABI/body results: PASS"
