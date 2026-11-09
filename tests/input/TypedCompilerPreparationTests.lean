import Miri.Input.CompilerConstantQueries
import Miri.Input.CompilerLifecycle
import Miri.Input.Decoder
import Miri.Input.LowerMIR

open Lean Miri.Input

private def must (value : Except String α) : IO α :=
  match value with | .ok result => pure result | .error message => throw (IO.userError message)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def tables (program : LoweredProgram) :=
  (program.bundle.spans, program.bundle.definitions, program.bundle.typeConstants)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected exporter MIR input")
  let input ← must (decodeJson (← IO.FS.readFile path))
  let program ← must (lowerProgram input.document)
  let constants ← must (CompilerConstantQueries.prepare program)
  check (tables constants.program == tables program) "constant preparation changed compiler pool IDs"
  check (!constants.evidence.isEmpty) "fixture contains no constant query evidence"
  for entry in constants.evidence do
    check (entry.site.bodyIndex < program.bundle.bodies.size && entry.query.span.id < program.bundle.spans.size)
      "prepared evidence lost its body or source span ID"
  let prepared := CompilerLifecycle.prepare program
  check (tables prepared.program == tables program) "lifecycle preparation changed compiler pool IDs"
  check (prepared.entries.size == program.bundle.bodies.size) "lifecycle entries changed body pool indexing"
  let some index := program.bundle.bodies.findIdx? (·.input.constantQueryContext.isSome)
    | throw (IO.userError "fixture contains no normalization query context")
  let some body := program.bundle.bodies[index]? | throw (IO.userError "body disappeared")
  let some context := body.input.constantQueryContext | throw (IO.userError "query context disappeared")
  let invalidBody := { body with input := { body.input with preambleDefSpanId := program.input.spans.size } }
  let invalid := { program with bundle := { program.bundle with bodies := program.bundle.bodies.set! index invalidBody } }
  let rejected := CompilerLifecycle.prepare invalid
  let some rejectedEntry := rejected.entries[index]? | throw (IO.userError "missing lifecycle entry")
  check (!rejectedEntry.preamble.isOk) "invalid source span became lifecycle evidence"
  check (tables rejected.program == tables program) "failed lifecycle preparation changed compiler pools"
  let invalidContext := { context with instanceId := program.input.instances.size }
  let invalidBody := { body with input := { body.input with constantQueryContext := some invalidContext } }
  let invalid := { program with bundle := { program.bundle with bodies := program.bundle.bodies.set! index invalidBody } }
  check (!(CompilerConstantQueries.prepare invalid).isOk) "out of bounds normalization instance was accepted"
  IO.println "constant and lifecycle preparation retain typed IDs and reject invalid source metadata"
