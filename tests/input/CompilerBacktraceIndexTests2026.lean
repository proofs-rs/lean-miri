import MiriTests.Input.LegacyFixture
import Miri.Input.CompilerBacktraceSource

open Miri Miri.Input Miri.Interpreter

private def must (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def replaceSpans (program : LoweredProgram) (index : Nat)
    (rows : Array BacktraceSpan) : Except String LoweredProgram := do
  let body ← SourceMir.resolveBody program.input index
  let some seed := program.input.bodies[index]? | throw "test body index absent"
  let material : Body := {toBodyCore := {body with backtraceSpans := rows}, promotedBodies := seed.promotedBodies}
  let bodies := program.input.bodies.set! index (.material material)
  pure {program with input := {program.input with bodies}}

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "producer export path required")
  let decoded ← must (decodeFixture (← IO.FS.readFile path))
  let program ← must (lowerProgram decoded.document)
  let baseline ← must (CompilerBacktraceSource.prepare program)
  let some firstIndex := (List.range program.bodyCount).toArray.find? (fun index =>
      ((program.bodyMetadata index).toOption.map fun body => !body.backtraceSpans.isEmpty).getD false)
    | throw (IO.userError "fixture has no executable body source-map rows")
  let firstBody ← must (program.bodyMetadata firstIndex)
  let some firstRow := firstBody.backtraceSpans[0]? | throw (IO.userError "source row disappeared")
  let some (.ok entries) := baseline.bodySpans[firstIndex]?
    | throw (IO.userError "baseline source rows failed")
  let some entry := entries[0]? | throw (IO.userError "baseline source row disappeared")
  check (entry.position.filename == firstRow.position.filename)
    "source preparation expanded or changed filename ID"
  let invalidFile := {firstRow with position :=
    {firstRow.position with filename := program.input.files.size}}
  let invalidProgram ← must (replaceSpans program firstIndex #[invalidFile])
  let invalidPrepared ← must (CompilerBacktraceSource.prepare invalidProgram)
  let some (.error fileError) := invalidPrepared.bodySpans[firstIndex]?
    | throw (IO.userError "invalid prepared filename ID accepted")
  check (fileError == "backtrace filename ID out of bounds")
    "invalid prepared filename diagnostic changed"
  let changed := {firstRow with position := {firstRow.position with line := firstRow.position.line + 1}}
  let conflicting ← must (replaceSpans program firstIndex (firstBody.backtraceSpans.push changed))
  let conflict ← must (CompilerBacktraceSource.prepare conflicting)
  let some (.error error) := conflict.bodySpans[firstIndex]? | throw (IO.userError "body conflict was accepted")
  check (error == "conflicting body/span hygiene query") "body conflict diagnostic changed"
  check (conflict.bodySpans.size == baseline.bodySpans.size) "body error stopped later body preparation"

  let some nextIndex := (List.range program.bodyCount).toArray.find? (· > firstIndex)
    | throw (IO.userError "fixture needs a later executable body")
  let mut cleared := program
  for index in (List.range program.bodyCount).toArray do
    cleared ← must (replaceSpans cleared index #[])
  let firstOnly ← must (replaceSpans cleared firstIndex #[firstRow])
  let crossConflict ← must (replaceSpans firstOnly nextIndex #[changed])
  match CompilerBacktraceSource.prepare crossConflict with
  | .error error => check (error == "conflicting exact source-map query") "cross-body conflict diagnostic changed"
  | .ok _ => throw (IO.userError "cross-body source-map conflict accepted")

  let bad := {firstRow with position := {firstRow.position with bytePosition := 2^32}}
  let failed ← must (replaceSpans cleared firstIndex #[firstRow, bad])
  let recovered ← must (replaceSpans failed nextIndex #[firstRow])
  let recovery ← must (CompilerBacktraceSource.prepare recovered)
  let some (.error error) := recovery.bodySpans[firstIndex]? | throw (IO.userError "invalid BytePos accepted")
  check (error == "compiler BytePos exceeds u32") "BytePos diagnostic changed"
  let some (.ok next) := recovery.bodySpans[nextIndex]? | throw (IO.userError "later body was not prepared")
  check (next.size == 1) "later body lost its exact source row"

  -- One global span can collapse differently in distinct inlined body contexts.
  let otherPosition := {firstRow with position :=
    {firstRow.position with bytePosition := firstRow.position.bytePosition + 1}}
  let distinct ← must (replaceSpans firstOnly nextIndex #[otherPosition])
  let distinctPrepared ← must (CompilerBacktraceSource.prepare distinct)
  let some (.ok firstEntries) := distinctPrepared.bodySpans[firstIndex]?
    | throw (IO.userError "first body collapsed source missing")
  let some (.ok nextEntries) := distinctPrepared.bodySpans[nextIndex]?
    | throw (IO.userError "second body collapsed source missing")
  check ((firstEntries[0]?).map (·.position.bytePosition) == some (UInt32.ofNat firstRow.position.bytePosition))
    "first body lost its collapsed BytePos"
  check ((nextEntries[0]?).map (·.position.bytePosition) == some (UInt32.ofNat otherPosition.position.bytePosition))
    "second body reused a global span position"

  let runtime := program.input.queries.runtime
  let some instanceRow := runtime.instances[0]? | throw (IO.userError "fixture needs a runtime instance")
  let changed := {instanceRow with display := instanceRow.display ++ "-conflict"}
  let queries := {program.input.queries with runtime := {runtime with instances := runtime.instances.push changed}}
  let nameConflict := {program with input := {program.input with queries}}
  match CompilerBacktraceSource.prepare nameConflict with
  | .error error => check (error == "conflicting compiler full-instance rendering") "instance name conflict diagnostic changed"
  | .ok _ => throw (IO.userError "full-instance name conflict accepted")
  IO.println "compiler backtrace preparation preserves conflicts and per-body recovery"
