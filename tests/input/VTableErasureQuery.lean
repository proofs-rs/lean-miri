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

private def rejects {α : Type} (result : Except String α) (expected : String) : IO Unit :=
  match result with
  | .error error => check (error == expected) s!"unexpected negative-case diagnostic: {error}"
  | .ok _ => throw (IO.userError s!"invalid vtable evidence accepted: {expected}")

private def checkMemoryAlias (runtime : CompilerVTableRuntime.Prepared)
    (rows : Array Catalog.VtableQuery) (parent : Catalog.VtableQuery) (ty allocation : Nat) : IO Unit := do
  let facts := runtime.facts
  check (facts.context.program.input.allocations.any fun node =>
    node.id == allocation && node.kind == .memory) "TraitVPtr control target is not memory-backed"
  let _ ← must (CompilerVTableRuntime.queryTargetPrincipal facts rows ty allocation)
  let targets := rows.toList.zipIdx.filter fun (row, _) => row.vtableAllocation == some allocation
  check (targets.length >= 2) "control lost its shared memory-backed vtable allocation"
  let some (target, index) := targets.head? | throw (IO.userError "missing target query")
  let alias := {parent with vtableAllocation := some allocation,
    metadata := {parent.metadata with entries := target.metadata.entries}}
  let conflict := "conflicting compiler vtable rows for exact allocation identity"
  rejects (CompilerVTableRuntime.queryTargetPrincipal facts (rows.push alias) ty allocation) conflict
  let missingSize := rows.set! index {target with metadata := {target.metadata with sizeBytes := none}}
  rejects (CompilerVTableRuntime.queryTargetPrincipal facts missingSize ty allocation)
    "memory-backed vtable size is absent"
  let missingAlign := rows.set! index {target with metadata := {target.metadata with alignBytes := none}}
  rejects (CompilerVTableRuntime.queryTargetPrincipal facts missingAlign ty allocation)
    "memory-backed vtable alignment is absent"
  let some size := target.metadata.sizeBytes | throw (IO.userError "vtable size absent")
  let wrongSize := {target with metadata := {target.metadata with sizeBytes := some (size + 1)}}
  let wrongRows := rows.set! index wrongSize
  rejects (CompilerVTableRuntime.queryTargetPrincipal facts wrongRows ty allocation) conflict
  let some id := target.metadata.principalPredicate | throw (IO.userError "vtable principal absent")
  let program := facts.context.program
  let missing := { program with input := { program.input with
    compilerPredicates := program.input.compilerPredicates.filter (·.id != id) } }
  let missingFacts := { facts with context := facts.context.withProgram missing }
  rejects (CompilerVTableRuntime.queryTargetPrincipal missingFacts rows ty allocation)
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
      IO.println s!"vtable_query_map query_id={id} input_type={entry.inputType} input_predicates={entry.inputPredicates} output_type={entry.outputType} output_predicates={entry.outputPredicates}"
  check (!queries.entries.isEmpty) "no compiler vtable queries: no coverage"
  if extra.contains "predicate-contrast" then
    check (queries.entries.any fun first => queries.entries.any fun second =>
      first.inputType == second.inputType && first.inputPredicates != second.inputPredicates &&
      first.outputType == second.outputType && first.outputPredicates != second.outputPredicates)
      "control lost its same-type/distinct-predicate contrast"
  if extra.contains "trait-vptr" then
    let rows := program.input.queries.vtables
    let mut found := false
    for row in rows do
      let ty := row.inputType
      let principal := row.metadata.principalPredicate
      let entries ← must (CompilerVTableRuntime.entries prepared.compiler.vtables.calls.symbols principal ty)
      if entries.any (fun entry => match entry with | .traitVPtr _ => true | _ => false) then
        found := true
        for entry in row.metadata.entries do
          if entry.kind == .supertraitVtablePointer then
            let some allocation := entry.allocationId | throw (IO.userError "TraitVPtr allocation missing")
            checkMemoryAlias prepared.compiler.vtables.calls.symbols rows row ty allocation
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
