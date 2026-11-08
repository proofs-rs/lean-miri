import Miri.Input.Decoder

/-! Regression for source-demand FnABI collection. Physical table membership
alone does not demand an ABI; abi_query does, in source traversal order. -/
open Lean Miri.Input
set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def put (object : Json) (key : String) (value : Json) : Except String Json := do
  let fields ← object.getObj?
  return Json.mkObj ((fields.toList.filter (fun entry => entry.1 != key)) ++ [(key, value)])

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected a fresh numeric input")
  let raw ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let baseline ← IO.ofExcept (decodeRuntimeJson raw.compress)
  let tables ← IO.ofExcept (raw.getObjVal? "semantic_tables")
  let abis ← IO.ofExcept ((← IO.ofExcept (tables.getObjVal? "function_abis")).getArr?)
  let mut probe? := none
  for sample in abis do
    let canUnwind ← IO.ofExcept (sample.getObjValAs? Bool "can_unwind")
    let candidate ← IO.ofExcept (put sample "can_unwind" (toJson (!canUnwind)))
    if !(abis.any (· == candidate)) && probe?.isNone then probe? := some candidate
  let some probe := probe? | throw (IO.userError "fixture has no unique can_unwind probe ABI")
  let tables ← IO.ofExcept (put tables "function_abis" (.arr (abis.push probe)))
  let unreferenced ← IO.ofExcept (put raw "semantic_tables" tables)
  let unused ← IO.ofExcept (decodeRuntimeJson unreferenced.compress)
  let payloads := baseline.document.functionAbis.map (·.payload)
  check (unused.document.functionAbis.map (·.payload) == payloads)
    "unreferenced physical catalog ABI changed source collection"
  let query := toJson abis.size
  let source ← IO.ofExcept (put unreferenced "collector_probe"
    (Json.mkObj [("abi_query", query), ("duplicate", Json.mkObj [("abi_query", query)])]))
  let demanded ← IO.ofExcept (decodeRuntimeJson source.compress)
  let demandedPayloads := demanded.document.functionAbis.map (·.payload)
  check (demandedPayloads.size == payloads.size + 1)
    "abi_query did not add exactly one resolved ABI"
  check ((demandedPayloads.filter (· == probe)).size == 1)
    "duplicate numeric ABI references were not deduplicated by payload"
  check ((demandedPayloads.filter (· != probe)) == payloads)
    "source ABI ordering changed after inserting a query"
  let malformed ← IO.ofExcept (put raw "collector_probe"
    (Json.mkObj [("fn_abi", Json.mkObj [("status", .str "supported")])]))
  check (!(decodeRuntimeJson malformed.compress).isOk && !(decodeJson malformed.compress).isOk)
    "nonnumeric fn_abi reference was accepted"
  IO.println "numeric ABI collector: catalog isolation; query lookup; payload dedup; source order"
