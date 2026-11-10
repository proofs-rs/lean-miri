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
  let prepared := CompilerLifecycle.prepare program
  check (tables prepared.program == tables program) "lifecycle preparation changed compiler pool IDs"
  check (prepared.entries.size == program.bundle.bodies.size) "lifecycle entries changed body pool indexing"
  let index := 0
  let some body := program.bundle.bodies[index]? | throw (IO.userError "fixture contains no body")
  check (body.input.instanceId < program.input.instances.size) "resolved body instance is absent"
  let invalidBody := { body with input := { body.input with preambleDefSpanId := program.input.spans.size } }
  let invalid := { program with bundle := { program.bundle with bodies := program.bundle.bodies.set! index invalidBody } }
  let rejected := CompilerLifecycle.prepare invalid
  let some rejectedEntry := rejected.entries[index]? | throw (IO.userError "missing lifecycle entry")
  check (!rejectedEntry.preamble.isOk) "invalid source span became lifecycle evidence"
  check (tables rejected.program == tables program) "failed lifecycle preparation changed compiler pools"
  let invalidBody := { body with input := { body.input with instanceId := program.input.instances.size } }
  let invalid := { program with bundle := { program.bundle with bodies := program.bundle.bodies.set! index invalidBody } }
  let rejected := CompilerLifecycle.prepare invalid
  let some entry := rejected.entries[index]? | throw (IO.userError "missing lifecycle entry")
  check (!entry.callee.isOk) "out of bounds body instance was accepted"
  IO.println "resolved lifecycle preparation retains typed IDs and rejects invalid source metadata"
