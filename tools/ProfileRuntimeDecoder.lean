import Miri.Input.Decoder

/-! Decode-only profiling; no guest execution or safety verdict. -/
open Lean Miri.Input

private def boundary (message : String) : IO Unit := do
  let out ← IO.getStdout
  out.putStrLn message
  out.flush

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: profile_runtime_decoder INPUT.json")
  let options := (({} : Options).setBool `profiler true).set `profiler.threshold (1 : Nat)
  boundary "decode: start"
  let text ← IO.FS.readFile path
  let decoded ← match decodeRuntimeJsonProfiled text options with
    | .ok value => pure value
    | .error reason => throw (IO.userError reason)
  unless decoded.executionInput.isSome && decoded.blockingObligations.isEmpty do
    throw (IO.userError s!"strict readiness gate failed: {decoded.blockingObligations.size} blocking obligations")
  boundary "decode: ready obligations=0"
  boundary s!"decode_only: complete bodies={decoded.document.bodies.size}; guest_execution=not_run; safety=not_evaluated"
