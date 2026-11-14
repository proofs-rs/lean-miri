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
  let some seed := program.input.bodies[index]? | throw "test body index absent"
  match seed with
  | .material body =>
    let bodies := program.input.bodies.set! index (.material {body with backtraceSpans := rows})
    pure {program with input := {program.input with bodies}}
  | .noopDrop _ => throw "test requires ordinary body metadata"
  | .copyTemplate reference =>
    let some source := program.input.mirTemplates[reference.templateId]?
      | throw "test template source absent"
    -- Clone this source metadata for the selected reference only. No executable
    -- body or execution-owned type ID is embedded into immutable input.
    let templateId := program.input.mirTemplates.size
    let mirTemplates := program.input.mirTemplates.push {source with backtraceSpans := rows}
    let bodies := program.input.bodies.set! index (.copyTemplate {reference with templateId})
    pure {program with input := {program.input with bodies, mirTemplates}}

private def collapse (world : RuntimeArrayTypes.World) (prepared : CompilerBacktraceSource.Prepared)
    (index span : Nat) : Except String UInt32 := do
  let world := {world with
    metadata := {world.metadata with source := prepared.program.input, checkedMaterial := none, denseTypes := none}
    bodies := BodyArena.Store.ofSource prepared.program.input.bodies}
  let access : RuntimeArrayQueries.Access RuntimeArrayTypes.World := ⟨id,fun _ next => next⟩
  match CompilerBacktraceSource.collapsedSpan prepared access (.ofCanonicalIndex index) ⟨span⟩ world with
  | .ok value _ => pure value
  | .error (.unsupported error) _ => throw error
  | .error error _ => throw (reprStr error)

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "producer export path required")
  let decoded ← must (decodeFixture (← IO.FS.readFile path))
  let program ← must (lowerProgram decoded.document)
  let baseline ← must (CompilerBacktraceSource.prepare program)
  let runtime ← must ((RuntimeMetadata.ofDocument program.input).mapError toString)
  let world ← must ((RuntimeArrayTypes.create runtime).mapError reprStr)
  let some firstIndex := (List.range program.bodyCount).toArray.find? (fun index =>
      ((program.bodyMetadata index).toOption.map fun body => !body.backtraceSpans.isEmpty).getD false)
    | throw (IO.userError "fixture has no executable body source-map rows")
  let firstBody ← must (program.bodyMetadata firstIndex)
  let some firstRow := firstBody.backtraceSpans[0]? | throw (IO.userError "source row disappeared")
  let baselinePosition ← must (collapse world baseline firstIndex firstRow.spanId)
  check (baselinePosition == UInt32.ofNat firstRow.position.bytePosition)
    "demand changed the exact body/span position"
  let invalidFile := {firstRow with position :=
    {firstRow.position with filename := program.input.files.size}}
  let invalidProgram ← must (replaceSpans program firstIndex #[invalidFile])
  let invalidPrepared ← must (CompilerBacktraceSource.prepare invalidProgram)
  check (!(collapse world invalidPrepared firstIndex firstRow.spanId).isOk)
    "invalid demanded filename ID accepted"
  let changed := {firstRow with position := {firstRow.position with line := firstRow.position.line + 1}}
  let conflicting ← must (replaceSpans program firstIndex (firstBody.backtraceSpans.push changed))
  let conflict ← must (CompilerBacktraceSource.prepare conflicting)
  match collapse world conflict firstIndex firstRow.spanId with
  | .error error => check (error.endsWith "conflicting body/span hygiene query") "body conflict diagnostic changed"
  | .ok _ => throw (IO.userError "demanded body conflict was accepted")

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
  check (!(collapse world recovery firstIndex firstRow.spanId).isOk)
    "invalid demanded BytePos accepted"
  check ((← must (collapse world recovery nextIndex firstRow.spanId)) == UInt32.ofNat firstRow.position.bytePosition)
    "later body lost its exact source row after an earlier demand error"

  -- One global span can collapse differently in distinct inlined body contexts.
  let otherPosition := {firstRow with position :=
    {firstRow.position with bytePosition := firstRow.position.bytePosition + 1}}
  let distinct ← must (replaceSpans firstOnly nextIndex #[otherPosition])
  let distinctPrepared ← must (CompilerBacktraceSource.prepare distinct)
  check ((← must (collapse world distinctPrepared firstIndex firstRow.spanId)) == UInt32.ofNat firstRow.position.bytePosition)
    "first body lost its collapsed BytePos"
  check ((← must (collapse world distinctPrepared nextIndex firstRow.spanId)) == UInt32.ofNat otherPosition.position.bytePosition)
    "second body reused a global span position"

  let runtime := program.input.queries.runtime
  let some instanceRow := runtime.instances[0]? | throw (IO.userError "fixture needs a runtime instance")
  let changed := {instanceRow with display := instanceRow.display ++ "-conflict"}
  let queries := {program.input.queries with runtime := {runtime with instances := runtime.instances.push changed}}
  let nameConflict := {program with input := {program.input with queries}}
  match CompilerBacktraceSource.prepare nameConflict with
  | .error error => check (error == "conflicting compiler full-instance rendering") "instance name conflict diagnostic changed"
  | .ok _ => throw (IO.userError "full-instance name conflict accepted")
  IO.println "compiler backtrace demand preserves exact body contexts, conflicts and recovery"
