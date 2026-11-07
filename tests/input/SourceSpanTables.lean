import Miri.Input.CompilerContextSpan
import Miri.Input.CompilerLifecycle

open Miri.Input

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "usage: SourceSpanTables <export.json>")
  let .ok decoded := decodeRuntimeJson (← IO.FS.readFile path)
    | throw (IO.userError "input decoding failed")
  let .ok program := lowerCoreProgram decoded.document
    | throw (IO.userError "input lowering failed")
  let .ok program := CompilerContextSpan.prepare program
    | throw (IO.userError "compiler root span unavailable")
  let prepared := CompilerLifecycle.prepare program
  for (entry, index) in prepared.entries.toList.zipIdx do
    let .ok _ := entry.preamble
      | throw (IO.userError s!"body {index}: compiler preamble span unavailable")
    let some body := prepared.program.bundle.bodies[index]?
      | throw (IO.userError "lifecycle body missing")
    let some id := body.input.span | throw (IO.userError s!"body {index}: body span absent")
    let .ok _ := prepared.program.input.sourceSpans.lookup id
      | throw (IO.userError s!"body {index}: body span has no table entry")
  let .ok _ := CompilerContextSpan.rootSpan prepared.program
    | throw (IO.userError "prepared root span missing")
  let invalid := {program with input := {program.input with rootSpan := some program.input.sourceSpans.size}}
  match CompilerContextSpan.prepare invalid with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "invalid root span ID accepted")
  IO.println s!"compiler span tables: PASS ({prepared.entries.size} root/instance/promoted bodies)"
