import Miri.Input.Decoder

open Lean Miri.Input

private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def set (value : Json) (key : String) (child : Json) : Except String Json := do
  let fields ← value.getObj?
  pure (Json.mkObj ((key, child) :: fields.toList.filter (fun item => item.1 != key)))

private def repeated (source leaf : Json) : Except String (Json × Nat) := do
  let catalog ← source.getObjVal? "semantic_tables"
  let nodes ← (← catalog.getObjVal? "generic_args").getArr?
  let id := nodes.size
  let parent := Json.arr #[Json.mkObj [("kind", .str "type"), ("value", leaf)]]
  let catalog ← set catalog "generic_args" (.arr (nodes.push parent))
  let source ← set source "semantic_tables" catalog
  let source ← set source "synthetic_shared_a" (Json.mkObj [("generic_args", toJson id)])
  let source ← set source "synthetic_shared_b" (Json.mkObj [("generic_args", toJson id)])
  let source ← set source "synthetic_shared_c" (Json.mkObj [("generic_args", toJson id)])
  return (source, id)

private def rejects (name : String) (source : Json) (expected : String) : IO Unit := do
  let text := source.compress
  match decodeJson text, decodeRuntimeJson text with
  | .error full, .error runtime =>
    check (full == expected && runtime == expected)
      s!"{name}: expected={expected}; full={full}; runtime={runtime}"
  | _, _ => throw (IO.userError s!"{name}: both decoders must reject")
  IO.println s!"PASS {name}: {expected}"

def main (args : List String) : IO Unit := do
  let directory ← match args with
    | [directory] => pure directory
    | _ => throw (IO.userError "expected directory containing numeric schema-4 cases")
  let valid ← must (Json.parse (← IO.FS.readFile s!"{directory}/valid-permuted-dense.json"))
  let (source, argsId) ← must (repeated valid (toJson (0 : Nat)))
  let full ← must (decodeJson source.compress)
  let runtime ← must (decodeRuntimeJson source.compress)
  check ((full.document.semanticTables.nodes .genericArgs).size == argsId + 1 &&
    (runtime.document.semanticTables.nodes .genericArgs).size == argsId + 1)
    "valid repeated references did not retain exactly one semantic node"
  check (full.document.raw == source && runtime.document.raw == source)
    "numeric references were expanded into JSON objects"
  IO.println "PASS repeated-valid-ID: shared parent and leaf accepted by both decoders"
  let huge : Nat := 2^100
  let (source, argsId) ← must (repeated valid (toJson huge))
  rejects "repeated-dangling-ID-first-path" source
    s!"$.semantic_tables.generic_args[{argsId}][0].value: dangling type reference {huge}"
  let (source, argsId) ← must (repeated valid (.str "bad"))
  rejects "repeated-malformed-ID-first-path" source
    s!"$.semantic_tables.generic_args[{argsId}][0].value: malformed numeric type reference (Natural number expected)"
  let duplicates ← must (Json.parse (← IO.FS.readFile s!"{directory}/duplicate-and-range-first.json"))
  let (source, _) ← must (repeated duplicates (toJson huge))
  rejects "duplicate-table-before-shared-dangling-ID" source "type IDs: duplicate IDs"
  for key in ["entry_instance", "fallback_instance", "instance"] do
    for malformed in [Json.str "bad", Json.mkObj [("status", .str "supported")]] do
      let source ← must (set valid "synthetic_instance_slot" (Json.mkObj [(key, malformed)]))
      rejects s!"malformed-{key}" source
        s!"$.synthetic_instance_slot.{key}: malformed instance ID (Natural number expected)"
  let unavailable := Json.mkObj [("status", .str "unsupported"), ("reason", .str "fixture unavailable")]
  let source ← must (set valid "synthetic_instance_slot" (Json.mkObj [("entry_instance", unavailable)]))
  check (!(decodeJson source.compress).isOk && !(decodeRuntimeJson source.compress).isOk)
    "structured unsupported instance evidence was accepted"
  let query (value : Json) := value
  for (key, nested, path) in [
      ("compiler_runtime_primitives", Json.mkObj [("arbitrary_name", toJson huge)], "compiler_runtime_primitives.arbitrary_name"),
      ("compiler_named_types", Json.mkObj [("arbitrary_name", query (toJson huge))], "compiler_named_types.arbitrary_name"),
      ("type_queries", Json.mkObj [("arbitrary_name", query (toJson huge))], "type_queries.arbitrary_name"),
      ("compiler_runtime_primitives", Json.mkObj [("ordering_enum", query (toJson huge))], "compiler_runtime_primitives.ordering_enum"),
      ("compiler_libc_type_layouts", Json.mkObj [("entries", Json.mkObj [("arbitrary_name", query (toJson huge))])], "compiler_libc_type_layouts.entries.arbitrary_name"),
      ("compiler_windows_type_layouts", Json.mkObj [("entries", Json.mkObj [("arbitrary_name", query (toJson huge))])], "compiler_windows_type_layouts.entries.arbitrary_name")] do
    let source ← must (set valid key nested)
    rejects s!"dangling-core-type-{path}" source s!"$.{path}: dangling type reference {huge}"
  for field in ["mut_pointer_type", "mut_reference_type", "drop_glue"] do
    let row := Json.mkObj [("input_type_id", toJson (0 : Nat)), (field, query (toJson huge))]
    let source ← must (set valid "synthetic_runtime_type" row)
    let kind := if field == "drop_glue" then "instance" else "type"
    rejects s!"dangling-core-{field}" source s!"$.synthetic_runtime_type.{field}: dangling {kind} reference {huge}"
  for kind in ["box_type", "resolve_fn_ptr", "resolve_closure_fn_once"] do
    let row := Json.mkObj [("query_kind", .str kind), ("value", toJson huge)]
    let source ← must (set valid "synthetic_cast_query" row)
    let referenceKind := if kind == "box_type" then "type" else "instance"
    rejects s!"dangling-core-{kind}" source s!"$.synthetic_cast_query.value: dangling {referenceKind} reference {huge}"
  let resolved := Json.mkObj [("original_instance_id", toJson (0 : Nat)),
    ("method_definition", toJson (0 : Nat)), ("resolved", query (toJson huge))]
  let source ← must (set valid "synthetic_virtual" resolved)
  rejects "dangling-core-virtual-resolution" source s!"$.synthetic_virtual.resolved: dangling instance reference {huge}"
  let source ← must (set valid "synthetic_static" (Json.mkObj [("allocation_query", query (toJson huge))]))
  rejects "dangling-static-allocation-query" source s!"$.synthetic_static.allocation_query: dangling allocation reference {huge}"
  let relocation := Json.mkObj [("storage_offset_bytes", toJson (0 : Nat)), ("target", toJson huge)]
  let source ← must (set valid "synthetic_relocation" relocation)
  rejects "dangling-relocation-target" source s!"$.synthetic_relocation.target: dangling allocation reference {huge}"
  let source ← must (set valid "covered_allocation_ids" (Json.arr #[toJson huge]))
  rejects "dangling-covered-allocation" source s!"$.covered_allocation_ids[0]: dangling allocation reference {huge}"
  let source ← must (set valid "existing_allocation" (toJson huge))
  rejects "dangling-existing-allocation" source s!"$.existing_allocation: dangling allocation reference {huge}"
  let source ← must (set valid "pattern" (toJson huge))
  rejects "dangling-pattern-reference" source s!"$.pattern: dangling patterns reference {huge}"
  let scalar := Json.mkObj [("query_kind", .str "supertrait_slot"), ("value", toJson huge)]
  let source ← must (set valid "synthetic_scalar_query" scalar)
  let full ← must (decodeJson source.compress)
  let runtime ← must (decodeRuntimeJson source.compress)
  check (full.executionInput.document.raw == runtime.executionInput.document.raw)
    "scalar supertrait-slot value was incorrectly bounded as an instance/type ID"
  IO.println "SharedIdReferenceChecks: schema-4 shared IDs and core query/dictionary bounds passed"
