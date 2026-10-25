import Miri.Input.EvalPreparation

/-! Diagnostic entry point for the existing, definitionally transparent decoder
and preparation profilers. This stops before guest execution and never reports
program safety. Build the library before using it with measure.py. -/
open Lean Miri.Input

private def boundary (message : String) : IO Unit := do
  let out ← IO.getStdout
  out.putStrLn message
  out.flush

private def must {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: ProfilePreparation INPUT.json")
  let profile := (({} : Options).setBool `profiler true).set `profiler.threshold (1 : Nat)
  boundary "decode: start"
  let text ← IO.FS.readFile path
  let decoded ← must (decodeRuntimeJsonProfiled text profile)
  unless decoded.executionInput.isSome && decoded.blockingObligations.isEmpty do
    throw (IO.userError s!"strict readiness gate failed: {decoded.blockingObligations.size} blocking obligations")
  boundary "decode: ready obligations=0"
  boundary "lower: start"
  let program ← must (lowerCoreProgram decoded.document)
  boundary "lower: complete"
  boundary s!"input_shape: types={program.input.types.size} instances={program.input.instances.size} bodies={program.bundle.bodies.size} allocations={program.input.allocations.size}"
  boundary "prepare: start"
  let prepared ← must (EvalPreparation.prepareProfiled profile program).outcome
  boundary "prepare: complete"
  let calls := prepared.compiler.lifecycle.calls.calls
  boundary s!"lookup_shape: call_sites={calls.entries.size} loaded_bodies={calls.bodies.size} function_facts={prepared.compiler.functions.functions.size} pointer_abis={prepared.compiler.functions.pointerAbis.size}"
  boundary s!"preparation_only: complete bodies={prepared.compiler.program.bundle.bodies.size}; guest_execution=not_run; safety=not_evaluated"
