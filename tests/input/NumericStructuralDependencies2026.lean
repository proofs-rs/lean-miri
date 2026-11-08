import Miri.Input.Decoder

/-! Synthetic source-demand probes derived from real compiler table nodes.
These check readiness dependency traversal only, without executing guest MIR. -/
open Lean Miri.Input
set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def put (object : Json) (key : String) (value : Json) : Except String Json := do
  let fields ← object.getObj?
  return Json.mkObj ((fields.toList.filter (fun entry => entry.1 != key)) ++ [(key, value)])

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def get (object : Json) (key : String) : IO Json := IO.ofExcept (object.getObjVal? key)
private def array (object : Json) (key : String) : IO (Array Json) := do
  IO.ofExcept ((← get object key).getArr?)
private def update (object : Json) (key : String) (value : Json) : IO Json := IO.ofExcept (put object key value)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected fresh numeric input")
  let raw ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let types ← array raw "types"
  let bodies ← array raw "bodies"
  let mut tables ← get raw "semantic_tables"
  let layouts ← array tables "layouts"
  let badLayout := layouts[0]!
  tables ← update tables "layouts" (.arr (layouts.push badLayout))
  let mut newType ← update types[0]! "type_id" (toJson types.size)
  newType ← update newType "layout" (toJson layouts.size)
  let mut base ← update raw "types" (.arr (types.push newType))
  -- A nested Or pattern follows pattern→constant→type semantic edges.
  let constants ← array tables "constants"
  let some constantSample := constants.find? (fun node =>
      (node.getObjValAs? String "kind").toOption == some "value") |
    throw (IO.userError "fixture has no typed pattern constant")
  let constant ← update constantSample "type" (toJson types.size)
  tables ← update tables "constants" (.arr (constants.push constant))
  let patterns ← array tables "patterns"
  let range := Json.mkObj [("kind", .str "range"),
    ("start", toJson constants.size), ("end", toJson constants.size)]
  let disjunction := Json.mkObj [("kind", .str "or"),
    ("patterns", .arr #[toJson patterns.size])]
  tables ← update tables "patterns" (.arr ((patterns.push range).push disjunction))
  -- An FnABI query follows FnABI→ArgABI→type semantic edges.
  let argAbis ← array tables "argument_abis"
  let argAbi ← update argAbis[0]! "type" (toJson types.size)
  tables ← update tables "argument_abis" (.arr (argAbis.push argAbi))
  let abis ← array tables "function_abis"
  let abi ← update abis[0]! "return" (toJson argAbis.size)
  tables ← update tables "function_abis" (.arr (abis.push abi))
  -- A fallback identity follows instance→generic args→type.
  let genericArgs ← array tables "generic_args"
  tables ← update tables "generic_args" (.arr (genericArgs.push (.arr #[
    Json.mkObj [("kind", .str "type"), ("value", toJson types.size)]])))
  let instances ← array raw "instances"
  let mut inst ← update instances[0]! "instance_id" (toJson instances.size)
  inst ← update inst "generic_args" (toJson genericArgs.size)
  inst ← update inst "def_path" (.str "synthetic::dependency_probe")
  base ← update base "instances" (.arr (instances.push inst))
  let allocations ← array raw "allocations"
  let some memory := allocations.find? (fun node =>
    (node.getObjValAs? String "kind").toOption == some "memory") |
    throw (IO.userError "fixture has no memory allocation")
  let mut allocation ← update memory "allocation_id" (toJson allocations.size)
  allocation ← update allocation "type" (toJson types.size)
  base ← update base "allocations" (.arr (allocations.push allocation))
  base ← update base "semantic_tables" tables
  -- Strict PR30 validates every type row, including unused physical rows.
  let invalidLayout ← update layouts[0]! "size_bytes" (.str "unsupported")
  let invalidTables ← update tables "layouts" (.arr (layouts.push invalidLayout))
  let invalid ← update base "semantic_tables" invalidTables
  check (!(decodeJson invalid.compress).isOk && !(decodeRuntimeJson invalid.compress).isOk)
    "unused malformed type layout passed the strict boundary"
  let unused ← IO.ofExcept (decodeRuntimeJson base.compress)
  check (unused.document.types.size == types.size + 1) "unreferenced synthetic type unexpectedly lost"
  let probes := #[
    ("or_pattern", Json.mkObj [("pattern", toJson (patterns.size + 1))]),
    ("abi_query", Json.mkObj [("abi_query", toJson abis.size)]),
    ("fallback_instance", Json.mkObj [("fallback_instance", toJson instances.size)]),
    ("relocation_target", Json.mkObj [("storage_offset_bytes", toJson (0 : Nat)), ("target", toJson allocations.size)]),
    ("allocation_array", Json.mkObj [("covered_allocation_ids", .arr #[toJson allocations.size])]),
    ("type_query", Json.mkObj [("query_kind", .str "box_type"), ("value", toJson types.size)])]
  for (name, probe) in probes do
    let body ← update bodies[0]! "dependency_probe" probe
    let source ← update base "bodies" (.arr (bodies.set! 0 body))
    let decoded ← IO.ofExcept (decodeRuntimeJson source.compress)
    check (decoded.document.types.size == types.size + 1)
      s!"{name}: valid transitive semantic references lost their target type"
    let invalid ← update source "semantic_tables" invalidTables
    check (!(decodeJson invalid.compress).isOk && !(decodeRuntimeJson invalid.compress).isOk)
      s!"{name}: malformed transitive target layout passed the strict boundary"
  IO.println "numeric structural dependencies: Or patterns; ABI query; fallback instance; relocation target; allocation array; contextual type query"
