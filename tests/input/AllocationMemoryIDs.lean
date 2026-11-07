import Miri.Input.Reader.AllocationMemory
import Miri.Input.Decoder
import Miri.Input.LowerMIR

open Lean Miri.Input

private def must (value : Except ε α) [ToString ε] : IO α :=
  match value with
  | .ok value => pure value
  | .error error => throw (IO.userError (toString error))

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def wrap (nodes : Array Json) (root : Json) : Json :=
  Json.mkObj [("shared_payloads", Json.mkObj [
    ("schema_version", toJson (2 : Nat)), ("nodes", Json.arr nodes)]), ("image", root)]

private def ref (id : Nat) : Json := Json.mkObj [("$lean_miri_shared_ref", toJson id)]

private def image (ranges relocations : Json) : Json :=
  Json.mkObj [("bytes_hex", toJson "00000000"), ("size_bytes", toJson (4 : Nat)),
    ("align_bytes", toJson (4 : Nat)), ("mutability", toJson "immutable"),
    ("initialization_ranges", ranges), ("relocations", relocations)]

private def range (first last : Nat) : Json :=
  Json.mkObj [("state", toJson "initialized"), ("start_bytes", toJson first),
    ("end_bytes_exclusive", toJson last)]

private def relocation (target : Json) (immutable shared : Bool) : Json :=
  Json.mkObj [("target", target), ("immutable", toJson immutable), ("shared_ref", toJson shared),
    ("target_offset_encoded_bytes", toJson "00000000"), ("storage_offset_bytes", toJson (0 : Nat))]

private def synthetic : IO Unit := do
  let target := Json.mkObj [("allocation_id", toJson (3 : Nat))]
  let reloc := relocation target true true
  let nodes := #[range 0 4, Json.arr #[ref 0], target,
    relocation (ref 2) true true, Json.arr #[ref 3], image (ref 1) (ref 4)]
  let catalog ← must (Reader.Catalog.parse (wrap nodes (ref 5)))
  let actual ← must (catalog.readAllocationMemory (ref 5) "image")
  let expected ← must (DecoderValues.parseAllocationMemory (image (.arr #[range 0 4]) (.arr #[reloc])) "image")
  require (actual == expected) "shared allocation storage changed"
  require (actual.relocations[0]?.map (·.target) == some 3) "relocation target changed"
  for bad in #[
      image (.arr #[range 1 4]) (.arr #[]),
      image (.arr #[range 0 5]) (.arr #[]),
      image (.arr #[range 0 3]) (.arr #[]),
      image (.arr #[range 0 4]) (.arr #[relocation
        (Json.mkObj [("allocation_id", toJson (2^64 - 1 : Nat))]) false false]),
      image (.arr #[range 0 4]) (.arr #[relocation (Json.mkObj [
        ("allocation_id", toJson (3 : Nat)), ("extra", .null)]) false false])] do
    let catalog ← must (Reader.Catalog.parse (wrap #[] bad))
    require (!(catalog.readAllocationMemory bad "image").isOk) "invalid allocation storage accepted"

private def diagnosticProjection (node : AllocationNode) : AllocationNode :=
  {node with data := node.data.map fun data => match data with
    | .function source => .function {source with genericArgs := .diagnostic .null}
    | .vtable source => .vtable {source with predicates := #[],entries := #[]}
    | other => other}

/-- Fields extracted from the source observation remain checked against their
executable typed tables, rather than being compared as erased diagnostics. -/
private def extractedSemantics (catalog : Reader.Catalog) (document : ImportDocumentCore)
    (raw : Json) (expected : AllocationNode) : IO Unit := do
  let compiler := document.mirTables.compiler
  let arguments := fun source => do
    let (args,next) ← must (lowerCompilerGenericArgs (LowerContext.ofDocument document) compiler source)
    require (next == compiler) "allocation oracle required unprepared compiler identities"
    pure args
  match expected.data with
  | some (.function source) =>
    let actual ← must ((document.mirTables.allocationFunctions.lookup expected.id).mapError fun _ => "allocation function absent")
    let actual ← must actual
    let definition ← must (lookupDefinitionId compiler.definitions source.definitionId)
    let args ← arguments source.genericArgs
    require (actual.instanceId == source.instanceId && actual.definitionId == source.definitionId &&
      actual.callee.defId == definition && actual.callee.args == args) "extracted allocation function semantics changed"
  | some (.vtable source) =>
    let some (some id) := document.vtableTables.allocationMetadata[expected.id]? |
      throw (IO.userError "allocation vtable metadata absent")
    let actual ← must ((document.vtableTables.metadata.lookup id).mapError fun _ => "vtable metadata absent")
    require (actual.status == expected.status && actual.typeId == source.typeId &&
      actual.layoutStatus == source.layoutStatus && actual.sizeBytes == source.sizeBytes && actual.alignBytes == source.alignBytes)
      "extracted vtable layout semantics changed"
    let predicates ← must ((document.vtableTables.predicateLists.lookup actual.predicates).mapError fun _ => "vtable predicates absent")
    let rawPredicates ← must (catalog.array (← must (catalog.field raw "predicates" "vtable")) "predicates")
    let expectedPredicates ← rawPredicates.mapM fun input => do must (catalog.natural
      (← must (catalog.field input "predicate_id" "predicate")) "predicate")
    require (predicates.values == expectedPredicates) "extracted vtable predicate identities or order changed"
    let entries ← must ((document.vtableTables.entryLists.lookup actual.entries).mapError fun _ => "vtable entries absent")
    require (entries.size == source.entries.size) "extracted vtable entry count changed"
    for (entry,index) in source.entries.toList.zipIdx do
      let some actual := entries[index]? | throw (IO.userError "vtable entry absent")
      require (actual.kind == entry.kind && actual.status == entry.status && actual.instanceId == entry.instanceId &&
        actual.allocationId == entry.allocationId) "extracted vtable entry semantics changed"
      if entry.kind == .method && entry.status == .supported then
        let some id := entry.instanceId | throw (IO.userError "vtable method instance absent")
        let callee ← must (document.mirTables.instance id)
        let some definition := entry.definitionId | throw (IO.userError "vtable method definition absent")
        let definition ← must (lookupDefinitionId compiler.definitions definition)
        let some sourceArgs := entry.genericArgs | throw (IO.userError "vtable method arguments absent")
        let args ← arguments sourceArgs
        require (callee.defId == definition && callee.args == args) "vtable method full-instance semantics changed"
  | _ => pure ()

def main (args : List String) : IO Unit := do
  synthetic
  let some path := args.head? | throw (IO.userError "usage: AllocationMemoryIDs <export.json>")
  let source ← IO.FS.readFile path
  let wire ← must (Json.parse source)
  let catalog ← must (Reader.Catalog.parse wire)
  let decoded ← must (decodeRuntimeJson source)
  let values ← must (catalog.array (← must (catalog.field catalog.root "allocations" "$")) "$.allocations")
  -- The original parser remains the storage oracle, with reader-local shared
  -- field lookups. Both models retain the same wire diagnostic payloads.
  let oracleValues := values
  let mut count := 0
  for (raw, index) in values.toList.zipIdx do
    let some node := decoded.document.allocations[index]? | throw (IO.userError "allocation absent")
    let some oracle := oracleValues[index]? | throw (IO.userError "allocation oracle absent")
    let expectedNode ← must (@DecoderValues.parseAllocation catalog.jsonFields oracle s!"$.allocations[{index}]")
    require (node == diagnosticProjection expectedNode) s!"allocation model changed at {index}"
    extractedSemantics catalog decoded.document raw expectedNode
    let test := fun raw expected => do
      let actual ← must (catalog.readAllocationMemory raw "allocation")
      require (actual == expected) s!"allocation storage semantics changed at {index}"
    match node.data with
    | some (.memory expected) => test raw expected; count := count + 1
    | some (.static value) =>
      if let some expected := value.initializer then
        test (← must (catalog.field raw "initializer" "allocation")) expected
        count := count + 1
    | _ => pure ()
  require (count > 0) "fixture lacks allocation images"
  let functions := decoded.document.allocations.foldl (fun count node =>
    match node.data with | some (.function _) => count + 1 | _ => count) (0 : Nat)
  let vtables := decoded.document.allocations.foldl (fun count node =>
    match node.data with | some (.vtable _) => count + 1 | _ => count) (0 : Nat)
  IO.println s!"allocation memory IDs: PASS ({count} exact storage images; {functions} functions; {vtables} vtables; malformed storage/provenance rejected)"
