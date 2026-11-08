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
      ("kind",.str "dynamic_vtable_upcast"),("status",.str "supported")])]
  compare "early-vtable-error" (set (set document "a_first" bad) "z_later" bad).compress
  let malformedAbi := Json.mkObj [("fn_abi",Json.mkObj [("status",.str "supported")])]
  compare "first-abi-error" (set (set document "a_first" malformedAbi) "z_later" malformedAbi).compress
  -- Cached and uncached readers reject failed shared nodes with the same
  -- physical transport-node diagnostic before any execution input exists.
  let issue := Json.mkObj [("kind", .str "synthetic_unknown"),
    ("status", .str "unsupported")]
  let .ok catalog := document.getObjVal? "shared_payloads" | throw (IO.userError "missing catalog")
  let .ok nodes := (catalog.getObjVal? "nodes").bind Json.getArr? | throw (IO.userError "missing nodes")
  let reference := Json.mkObj [("$lean_miri_shared_ref", toJson nodes.size)]
  let withNode := set document "shared_payloads" (set catalog "nodes" (.arr (nodes.push issue)))
  let contexts := Json.mkObj [("plain", reference), ("region", reference),
    ("hir_id", reference), ("coverage", reference),
    ("cast_kind", Json.mkObj [("coercion", reference)]),
    ("operand", reference), ("rvalue", reference), ("projection", reference),
    ("inline", issue), ("array", .arr #[reference, issue, reference])]
  let repeated := set (set withNode "synthetic_a" contexts) "synthetic_z.%[" contexts
  compare "shared-runtime-contexts-and-rebased-paths" repeated.compress
  match decodeRuntimeJson repeated.compress with
  | .error message =>
    unless message.endsWith "exporter payload status `unsupported` is not a successful input" do
      throw (IO.userError s!"failed shared payload must be rejected: {message}")
  | .ok _ => throw (IO.userError "failed shared payload was accepted")
  IO.println "cached/uncached decoder diagnostics and ordered ABI/body results: PASS"
