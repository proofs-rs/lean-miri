import Miri.Input.EvalPreparation

/-! Check genuine compiler query identities, separately from guest execution.
`nonidentity` rejects an export unless its complete type/predicate pair changes.
It must not turn an already-normalized HRTB control into branch coverage. -/
open Lean Miri Miri.Input Miri.Memory Miri.Interpreter

private def must {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def rejects {α : Type} (result : Except String α) (label : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"invalid vtable evidence accepted: {label}")

private def checkMemoryAlias (runtime : CompilerVTableRuntime.Prepared)
    (parent : Json) (ty allocation : Nat) : IO Unit := do
  let facts := runtime.facts
  let program := facts.context.program
  let tables := program.input.vtableTables
  check (program.input.allocations.any fun node =>
    node.id == allocation && node.kind == .memory) "TraitVPtr control target is not memory-backed"
  let _ ← must (CompilerVTableRuntime.queryTargetPrincipal facts ty allocation)
  let targets := tables.queries.toList.zipIdx.filterMap fun (entry,index) => do
    let row ← entry.toOption
    if row.allocationId == some allocation then some (row,index) else none
  check (targets.length >= 2) "control lost its shared memory-backed vtable allocation"
  let some (target,index) := targets.head? | throw (IO.userError "missing target query")
  let parentId ← must (parent.getObjValAs? Nat "query_id")
  let some parent := tables.queries.findSome? (fun row => do
      let row ← row.toOption
      if row.queryId == some parentId then some row else none)
    | throw (IO.userError "parent query absent")
  let some parentMetadataId := parent.metadata | throw (IO.userError "parent metadata absent")
  let some targetMetadataId := target.metadata | throw (IO.userError "target metadata absent")
  let metadata ← must ((tables.metadata.lookup targetMetadataId).mapError (fun _ => "target metadata missing"))
  let parentMetadata ← must ((tables.metadata.lookup parentMetadataId).mapError (fun _ => "parent metadata missing"))
  let withTables := fun tables =>
    {facts with context := facts.context.withProgram {program with input := {program.input with vtableTables := tables}}}
  let aliasId := tables.metadata.size
  let aliasMetadata := tables.metadata.push (some {parentMetadata with entries := metadata.entries})
  let alias := {parent with allocationId := some allocation, metadata := some aliasId}
  rejects (CompilerVTableRuntime.queryTargetPrincipal (withTables {tables with
    metadata := aliasMetadata, queries := tables.queries.push (.ok alias)}) ty allocation) "principal alias"
  let some size := metadata.sizeBytes | throw (IO.userError "target size missing")
  let wrongMetadata := tables.metadata.push (some {metadata with sizeBytes := some (size+1)})
  let wrongRows := tables.queries.mapIdx fun position row =>
    if position == index then .ok {target with metadata := some aliasId} else row
  rejects (CompilerVTableRuntime.queryTargetPrincipal (withTables {tables with
    metadata := wrongMetadata, queries := wrongRows}) ty allocation) "size conflict"
  let some id := metadata.principal | throw (IO.userError "principal absent")
  let missing := {program with input := {program.input with
    compilerPredicates := program.input.compilerPredicates.filter (·.id != id)}}
  let missingFacts := {facts with context := facts.context.withProgram missing}
  rejects (CompilerVTableRuntime.queryTargetPrincipal missingFacts ty allocation) "missing normalization evidence"
  IO.println "vtable-erasure: memory alias, layout and missing-evidence negative cases PASS"

def main (args : List String) : IO Unit := do
  let path :: mode :: extra := args |
    throw (IO.userError "usage: VTableErasureQuery <export.json> identity|nonidentity [predicate-contrast] [trait-vptr] [trace-map]")
  check (mode == "identity" || mode == "nonidentity") "unknown erasure expectation"
  check (extra.all fun flag => flag == "predicate-contrast" || flag == "trait-vptr" || flag == "trace-map")
    "unknown query coverage expectation"
  let decoded ← must (decodeJson (← IO.FS.readFile path))
  let program ← must (lowerProgram decoded.document)
  let attempt := EvalPreparation.prepare program
  let prepared ← must attempt.outcome
  let queries := prepared.compiler.vtables.queries
  if extra.contains "trace-map" then
    for entry in queries.entries do
      let some id := entry.diagnosticQueryId | throw (IO.userError "query trace lacks compiler query_id")
      IO.println s!"vtable_query_map query_id={id} input_type={entry.inputType} input_token={entry.inputPredicates} output_type={entry.outputType} output_token={entry.outputPredicates}"
  check (!queries.entries.isEmpty) "no compiler vtable queries: no coverage"
  if extra.contains "predicate-contrast" then
    check (queries.entries.any fun first => queries.entries.any fun second =>
      first.inputType == second.inputType && first.inputPredicates != second.inputPredicates &&
      first.outputType == second.outputType && first.outputPredicates != second.outputPredicates)
      "control lost its same-type/distinct-predicate contrast"
  if extra.contains "trait-vptr" then
    let rows ← must ((program.input.raw.getObjVal? "compiler_vtable_queries").bind Lean.Json.getArr?)
    let mut found := false
    for row in rows do
      let ty ← must ((row.getObjVal? "input_type").bind fun value => value.getObjValAs? Nat "type_id")
      let principal ← must ((row.getObjVal? "vtable_metadata").bind fun value =>
        value.getObjVal? "principal_predicate")
      let principal ← if principal == .null then pure none else
        some <$> must (principal.getObjValAs? Nat "predicate_id")
      let entries ← must (CompilerVTableRuntime.entries prepared.compiler.vtables.calls.symbols principal ty)
      if entries.any (fun entry => match entry with | .traitVPtr _ => true | _ => false) then
        found := true
        let sourceEntries ← must ((row.getObjVal? "vtable_metadata").bind fun metadata =>
          (metadata.getObjVal? "entries").bind Json.getArr?)
        for value in sourceEntries do
          let entry ← must (decodeVtableEntry value "$.vtable-erasure-control")
          if entry.kind == .supertraitVtablePointer then
            let some allocation := entry.allocationId | throw (IO.userError "TraitVPtr allocation missing")
            checkMemoryAlias prepared.compiler.vtables.calls.symbols row ty allocation
    check found "control has no consumer-resolved TraitVPtr entry"
    IO.println "vtable-erasure: consumer-resolved TraitVPtr PASS"
  let mut changed := 0
  for entry in queries.entries do
    let output := (entry.outputType, entry.outputPredicates)
    check ((← must (CompilerVTableQueries.eraseAndAnonymize queries
      entry.inputType entry.inputPredicates)) == output) "complete-pair lookup changed"
    check ((← must (CompilerVTableQueries.eraseAndAnonymize queries
      entry.outputType entry.outputPredicates)) == output) "canonical output query is not closed/idempotent"
    let removed := { queries with entries := queries.entries.filter fun other =>
      !(other.inputType == entry.inputType && other.inputPredicates == entry.inputPredicates) }
    match CompilerVTableQueries.eraseAndAnonymize removed entry.inputType entry.inputPredicates with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "missing exact query key was accepted")
    if (entry.inputType, entry.inputPredicates) != output then changed := changed + 1
  IO.println s!"vtable-erasure: queries={queries.entries.size}; nonidentity={changed}; predicate-contrast-required={extra.contains "predicate-contrast"}"
  check (if mode == "identity" then changed == 0 else changed > 0)
    s!"erasure expectation {mode} failed: nonidentity={changed}"
  let memory := attempt.memory
  let some world := program.input.compilerAllocIdWorld |
    throw (IO.userError "missing prepared allocation world")
  let registry ← must (CompilerVTableMachine.seedImported
    prepared.compiler.vtables prepared.image memory VTableMachine.Registry.empty)
  let rows := world.dedupCatalog.filter (·.keyKind == .vtable)
  check (!rows.isEmpty) "no prepared vtable salt rows"
  for row in rows do
    let keyRuntime ← must (AllocationImage.runtimeId memory row.keyAllocationId)
    let some key ← must (CompilerVTableRuntime.globalVTable
      prepared.compiler.vtables.calls.symbols prepared.image memory keyRuntime) |
      throw (IO.userError "catalog key has no exact type/predicate identity")
    check (queries.entries.any fun entry =>
      (entry.outputType, entry.outputPredicates) == key) "catalog key lacks canonical query output"
    check (row.salts.size == 32) "vtable row does not cover 32 salts"
    for salt in List.range 32 do
      let results := row.salts.filter (·.salt == salt)
      check (results.size == 1) s!"missing/duplicate salt {salt}"
      for result in results do
        let runtime ← must (AllocationImage.runtimeId memory result.allocationId)
        check (memory.sourceAllocIdForRuntime? runtime == some result.sourceAllocId)
          "raw/dense/runtime allocation crosswalk differs"
        check (registry.entries.any fun entry => entry.typeId == key.1 &&
          entry.dynamicType == key.2 && entry.salt.val == salt && entry.allocation == runtime)
          "salt result does not join the exact type/predicate runtime key"
  IO.println s!"vtable-erasure: exact catalog joins PASS; keys={rows.size}; salts-per-key=32"
