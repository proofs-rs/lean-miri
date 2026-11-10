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
  let some body := program.bundle.bodies[index]? | throw "test body index absent"
  let bodies := program.bundle.bodies.set! index {body with input := {body.input with backtraceSpans := rows}}
  pure {program with bundle := {program.bundle with bodies}}

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "producer export path required")
  let decoded ← must (decodeJson (← IO.FS.readFile path))
  let program ← must (lowerProgram decoded.document)
  let baseline ← must (CompilerBacktraceSource.prepare program)
  let some firstIndex := (List.range program.bundle.bodies.size).toArray.find? (fun index =>
      ((program.bundle.bodies[index]?).map fun body => !body.input.backtraceSpans.isEmpty).getD false)
    | throw (IO.userError "fixture has no executable body source-map rows")
  let some firstBody := program.bundle.bodies[firstIndex]? | throw (IO.userError "body disappeared")
  let some firstRow := firstBody.input.backtraceSpans[0]? | throw (IO.userError "source row disappeared")
  let changed := {firstRow with position := {firstRow.position with line := firstRow.position.line + 1}}
  let conflicting ← must (replaceSpans program firstIndex (firstBody.input.backtraceSpans.push changed))
  let conflict ← must (CompilerBacktraceSource.prepare conflicting)
  let some (.error error) := conflict.bodySpans[firstIndex]? | throw (IO.userError "body conflict was accepted")
  check (error == "conflicting body/span hygiene query") "body conflict diagnostic changed"
  check (conflict.bodySpans.size == baseline.bodySpans.size) "body error stopped later body preparation"

  let some nextIndex := (List.range program.bundle.bodies.size).toArray.find? (· > firstIndex)
    | throw (IO.userError "fixture needs a later executable body")
  let mut cleared := program
  for index in (List.range program.bundle.bodies.size).toArray do
    cleared ← must (replaceSpans cleared index #[])
  let firstOnly ← must (replaceSpans cleared firstIndex #[firstRow])
  let crossConflict ← must (replaceSpans firstOnly nextIndex #[changed])
  match CompilerBacktraceSource.prepare crossConflict with
  | .error error => check (error == "conflicting exact source-map query") "cross-body conflict diagnostic changed"
  | .ok _ => throw (IO.userError "cross-body source-map conflict accepted")

  let bad := {firstRow with collapsedLo := firstRow.collapsedLo + 1}
  let failed ← must (replaceSpans cleared firstIndex #[firstRow, bad])
  let recovered ← must (replaceSpans failed nextIndex #[firstRow])
  let recovery ← must (CompilerBacktraceSource.prepare recovered)
  let some (.error error) := recovery.bodySpans[firstIndex]? | throw (IO.userError "invalid collapsed position accepted")
  check (error == "collapsed hygiene BytePos/source-map position mismatch") "collapsed position diagnostic changed"
  let some (.ok next) := recovery.bodySpans[nextIndex]? | throw (IO.userError "later body was not prepared")
  check (next.size == 1) "later body lost its exact source row"

  let runtime := program.input.queries.runtime
  let some instanceRow := runtime.instances[0]? | throw (IO.userError "fixture needs a runtime instance")
  let changed := {instanceRow with display := instanceRow.display ++ "-conflict"}
  let queries := {program.input.queries with runtime := {runtime with instances := runtime.instances.push changed}}
  let nameConflict := {program with input := {program.input with queries}}
  match CompilerBacktraceSource.prepare nameConflict with
  | .error error => check (error == "conflicting compiler full-instance rendering") "instance name conflict diagnostic changed"
  | .ok _ => throw (IO.userError "full-instance name conflict accepted")
  IO.println "compiler backtrace preparation preserves conflicts and per-body recovery"
