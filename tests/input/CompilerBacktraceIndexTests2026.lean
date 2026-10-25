import Miri.Input.CompilerBacktraceSource

/-! Compatibility checks for the indexed compiler backtrace preparation path.
The executable accepts a retained producer export, compares indexed preparation
with the former ordered scans, and exercises body rollback and conflict errors. -/
open Lean Miri Miri.Input Miri.Interpreter

private def must (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def field (j : Json) (key : String) : Except String Json := j.getObjVal? key

private def setField (j : Json) (key : String) (value : Json) : Except String Json := do
  match j with
  | .obj fields =>
    let retained := fields.toList.filter fun entry => entry.1 != key
    pure (Json.mkObj ((key, value) :: retained))
  | _ => throw "expected object while mutating backtrace test fixture"

private def natural (j : Json) (key : String) : Except String Nat := do
  (← field j key).getNat?

private def legacyPosition (j : Json) : Except String CompilerBacktraceSource.Position := do
  let offset ← natural j "byte_position"
  unless offset < 2^32 do throw "compiler BytePos exceeds u32"
  return ⟨UInt32.ofNat offset, ← natural j "line", ← natural j "zero_based_char_column",
    ← (← field j "filename").getStr?⟩

private def legacySpans (tables : CompilerTables) (payload : Json) :
    Except String (Array CompilerBacktraceSource.SpanEntry × CompilerTables) := do
  let records ← (← field payload "backtrace_spans").getArr?
  let mut tables := tables
  let mut entries := #[]
  for record in records do
    let (span,next) ← lowerCompilerSpan tables (← decodeCompilerValue (← field record "span"))
    tables := next
    let location ← legacyPosition (← field record "source_position")
    unless (← natural record "collapsed_lo") == location.bytePosition.toNat do
      throw "collapsed hygiene BytePos/source-map position mismatch"
    if let some old := entries.find? (fun entry : CompilerBacktraceSource.SpanEntry => entry.span == span) then
      unless old.position == location do throw "conflicting body/span hygiene query"
    else entries := entries.push ⟨span,location⟩
  return (entries,tables)

private def legacyPrepare (program : LoweredProgram) : Except String CompilerBacktraceSource.Prepared := do
  let mut tables := program.compilerTables
  let mut bodySpans := #[]
  let mut positions := #[]
  for body in program.bundle.bodies do
    match legacySpans tables body.input.payload with
    | .error error => bodySpans := bodySpans.push (.error error)
    | .ok (entries,next) =>
      tables := next
      bodySpans := bodySpans.push (.ok entries)
      for entry in entries do
        if let some old := positions.find? (fun p : CompilerBacktraceSource.Position =>
            p.bytePosition == entry.position.bytePosition) then
          unless old == entry.position do throw "conflicting exact source-map query"
        else positions := positions.push entry.position
  let ctx := LowerContext.ofDocument program.input
  let records ← (← (← field program.input.raw "compiler_runtime_queries").getObjVal? "instances").getArr?
  let mut names := #[]
  for record in records do
    let (callee,next) ← CompilerInstance.decode ctx tables record
    tables := next
    let name ← (← field record "display").getStr?
    if let some (_,old) := names.find? (fun entry : CallInstance × String => entry.1 == callee) then
      unless old == name do throw "conflicting compiler full-instance rendering"
    else names := names.push (callee,name)
  return ⟨program.withCompilerTables tables,bodySpans,positions,names⟩

private def signature (result : Except String CompilerBacktraceSource.Prepared) : String :=
  match result with
  | .error error => "error:" ++ error
  | .ok prepared =>
    let bodyKeys := prepared.bodySpans.map fun result =>
      match result with
      | .error error => Except.error error
      | .ok entries => Except.ok (entries.map fun entry : CompilerBacktraceSource.SpanEntry =>
          (entry.span.id, entry.position.bytePosition, entry.position.line,
            entry.position.column, entry.position.filename))
    reprStr (prepared.program.compilerTables.spans, prepared.program.compilerTables.definitions,
      prepared.program.compilerTables.typeConstants, bodyKeys,
      prepared.positions.map fun p => (p.bytePosition,p.line,p.column,p.filename), prepared.names)

private def replaceBodyPayload (program : LoweredProgram) (index : Nat) (payload : Json) :
    Except String LoweredProgram := do
  let some body := program.bundle.bodies[index]? | throw "test body index absent"
  let bodies := program.bundle.bodies.set! index { body with input := { body.input with payload } }
  return { program with bundle := { program.bundle with bodies } }

private def replaceBacktraceSpans (program : LoweredProgram) (index : Nat)
    (records : Array Json) : Except String LoweredProgram := do
  let some body := program.bundle.bodies[index]? | throw "test body index absent"
  let payload ← setField body.input.payload "backtrace_spans" (.arr records)
  replaceBodyPayload program index payload

private def mutateInstanceName (program : LoweredProgram) (record : Json) : Except String LoweredProgram := do
  let queries ← field program.input.raw "compiler_runtime_queries"
  let records ← (← field queries "instances").getArr?
  let queries ← setField queries "instances" (.arr (records.push record))
  let raw ← setField program.input.raw "compiler_runtime_queries" queries
  return { program with input := { program.input with raw } }

private def hasBacktraceRows (body : LoweredBody) : Bool :=
  match (body.input.payload.getObjVal? "backtrace_spans").bind Json.getArr? with
  | .ok rows => !rows.isEmpty
  | .error _ => false

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "retained producer export path required")
  let decoded ← must (decodeRuntimeJson (← IO.FS.readFile path))
  let program ← must (lowerCoreProgram decoded.document)
  check (signature (CompilerBacktraceSource.prepare program) == signature (legacyPrepare program))
    "ordinary preparation differs from ordered scan reference"

  let some firstBodyIndex := (program.bundle.bodies.toList.zipIdx.find? fun (body, _) =>
      hasBacktraceRows body).map Prod.snd
    | throw (IO.userError "fixture has no body source-map rows")
  let some firstBody := program.bundle.bodies[firstBodyIndex]?
    | throw (IO.userError "selected body index disappeared")
  let sourceRowsJson ← must (field firstBody.input.payload "backtrace_spans")
  let sourceRows ← must (sourceRowsJson.getArr?)
  let some firstRow := sourceRows[0]?
    | throw (IO.userError "selected body source-map row disappeared")

  let sourcePosition ← must (field firstRow "source_position")
  let line ← must (natural sourcePosition "line")
  let changedPosition ← must (setField sourcePosition "line" (toJson (line + 1)))
  let conflictingRow ← must (setField firstRow "source_position" changedPosition)
  let conflictProgram ← must (replaceBacktraceSpans program firstBodyIndex
    (sourceRows.push conflictingRow))
  let indexedConflict := CompilerBacktraceSource.prepare conflictProgram
  let scanConflict := legacyPrepare conflictProgram
  check (signature indexedConflict == signature scanConflict)
    "duplicate body/span conflict changed diagnostic"
  let .ok conflictPrepared := indexedConflict
    | throw (IO.userError "body/span conflict unexpectedly aborted whole preparation")
  let some (.error bodyError) := conflictPrepared.bodySpans[firstBodyIndex]?
    | throw (IO.userError "duplicate body/span conflict was not recorded on its body")
  check (bodyError == "conflicting body/span hygiene query")
    "duplicate body/span conflict changed its exact diagnostic"
  check (conflictPrepared.bodySpans[firstBodyIndex + 1]?.isSome)
    "body/span conflict prevented later body preparation"

  check (program.bundle.bodies.size > firstBodyIndex + 1)
    "fixture needs a later body for the rollback check"
  let nextIndex := firstBodyIndex + 1
  let mut positionConflictProgram := program
  for index in [:firstBodyIndex] do
    positionConflictProgram ← must (replaceBacktraceSpans positionConflictProgram index #[])
  positionConflictProgram ← must (replaceBacktraceSpans positionConflictProgram firstBodyIndex #[firstRow])
  positionConflictProgram ← must (replaceBacktraceSpans positionConflictProgram nextIndex #[conflictingRow])
  let indexedPositionConflict := CompilerBacktraceSource.prepare positionConflictProgram
  let scanPositionConflict := legacyPrepare positionConflictProgram
  check (signature indexedPositionConflict == signature scanPositionConflict)
    "cross-body same-offset conflict changed diagnostic"
  let .error positionError := indexedPositionConflict
    | throw (IO.userError "cross-body same-offset conflict was accepted")
  check (positionError == "conflicting exact source-map query")
    "cross-body same-offset conflict did not retain its exact diagnostic"

  let spanJson ← must (field firstRow "span")
  let changedSpan ← must (setField spanJson "ctxt" (toJson "rollback-only-span"))
  let novelRow ← must (setField firstRow "span" changedSpan)
  let collapsedLo ← must (natural firstRow "collapsed_lo")
  let badRow ← must (setField firstRow "collapsed_lo" (toJson (collapsedLo + 1)))
  let rollbackProgram ← must (replaceBacktraceSpans program firstBodyIndex #[novelRow,badRow])
  let rollbackProgram ← must (replaceBacktraceSpans rollbackProgram nextIndex #[firstRow])
  let rollbackResult := CompilerBacktraceSource.prepare rollbackProgram
  check (signature rollbackResult == signature (legacyPrepare rollbackProgram))
    "failed-body span interning leaked into the next body"
  let .ok rollbackPrepared := rollbackResult
    | throw (IO.userError "rollback fixture unexpectedly aborted whole preparation")
  let some (.error rollbackError) := rollbackPrepared.bodySpans[firstBodyIndex]?
    | throw (IO.userError "rollback fixture's malformed body was not retained as a body error")
  check (rollbackError == "collapsed hygiene BytePos/source-map position mismatch")
    "rollback fixture did not trigger the expected later-record error"
  let some (.ok nextEntries) := rollbackPrepared.bodySpans[nextIndex]?
    | throw (IO.userError "body after rollback fixture was not prepared")
  check (nextEntries.size == 1) "body after rollback fixture lost its exact source row"

  let instanceRows := ((program.input.raw.getObjVal? "compiler_runtime_queries").bind
    (fun queries => queries.getObjVal? "instances") >>= Json.getArr?).toOption.getD #[]
  let some record := instanceRows[0]? | throw (IO.userError "fixture needs a runtime instance name row")
  let name ← must (field record "display")
  let duplicate ← must (setField record "display"
    (.str ((name.getStr?.toOption.getD "") ++ "-conflict")))
  let nameConflictProgram ← must (mutateInstanceName program duplicate)
  let indexedNameConflict := CompilerBacktraceSource.prepare nameConflictProgram
  let scanNameConflict := legacyPrepare nameConflictProgram
  check (signature indexedNameConflict == signature scanNameConflict)
    "duplicate full-instance name conflict changed diagnostic"
  check (indexedNameConflict.toOption.isNone) "duplicate full-instance name conflict was accepted"

  IO.println "indexed compiler backtrace preparation matches ordered scans and preserves conflicts/rollback"
