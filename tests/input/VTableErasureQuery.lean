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

private def replaceField (value : Json) (key : String) (replacement : Json) : Json :=
  match value with
  | .obj fields => Json.mkObj (fields.toList.map fun (name, old) =>
      (name, if name == key then replacement else old))
  | _ => value

private def rejects {α : Type} (result : Except String α) (expected : String) : IO Unit :=
  match result with
  | .error error => check (error == expected) s!"unexpected negative-case diagnostic: {error}"
  | .ok _ => throw (IO.userError s!"invalid vtable evidence accepted: {expected}")

private def checkMemoryAlias (runtime : CompilerVTableRuntime.Prepared) (raw : Json)
    (rows : Array Json) (parent : Json) (ty allocation : Nat) : IO Unit := do
  let facts := runtime.facts
  check (facts.context.program.input.allocations.any fun node =>
    node.id == allocation && node.kind == .memory) "TraitVPtr control target is not memory-backed"
  let _ ← must (CompilerVTableRuntime.queryTargetPrincipal facts raw ty allocation)
  let targets := rows.toList.zipIdx.filter fun (row, _) =>
    (row.getObjValAs? Nat "vtable_allocation_id").toOption == some allocation
  check (targets.length >= 2) "control lost its shared memory-backed vtable allocation"
  let some (target, index) := targets.head? | throw (IO.userError "missing target query")
  let metadata ← must (target.getObjVal? "vtable_metadata")
  let parentMetadata ← must (parent.getObjVal? "vtable_metadata")
  let entries ← must (metadata.getObjVal? "entries")
  -- Give an unrelated principal the same physical allocation and entry shape.
  -- Equal concrete type/layout/entries cannot replace normalization evidence.
  let alias := replaceField (replaceField parent "vtable_allocation_id" (toJson allocation))
    "vtable_metadata" (replaceField parentMetadata "entries" entries)
  let aliasRows := rows.push alias
  let conflict := "conflicting compiler vtable rows for exact allocation identity"
  rejects (CompilerVTableRuntime.queryTargetPrincipal facts
    (replaceField raw "compiler_vtable_queries" (.arr aliasRows)) ty allocation) conflict
  let size ← must (metadata.getObjValAs? Nat "size_bytes")
  let wrongSize := replaceField target "vtable_metadata" (replaceField metadata "size_bytes" (toJson (size + 1)))
  let wrongRows := rows.mapIdx fun position row => if position == index then wrongSize else row
  rejects (CompilerVTableRuntime.queryTargetPrincipal facts
    (replaceField raw "compiler_vtable_queries" (.arr wrongRows)) ty allocation) conflict
  let principal ← must (metadata.getObjVal? "principal_predicate")
  let id ← must (principal.getObjValAs? Nat "predicate_id")
  let program := facts.context.program
  let missing := { program with input := { program.input with
    compilerPredicates := program.input.compilerPredicates.filter (·.id != id) } }
  let missingFacts := { facts with context := facts.context.withProgram missing }
  rejects (CompilerVTableRuntime.queryTargetPrincipal missingFacts raw ty allocation)
    "memory-backed vtable principal normalization evidence missing"
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
            checkMemoryAlias prepared.compiler.vtables.calls.symbols program.input.raw rows row ty allocation
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
