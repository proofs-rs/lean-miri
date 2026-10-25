import Miri.Input

open Miri.Input

def main (args : List String) : IO Unit := do
  let some mode := args.head? | throw (IO.userError "usage: RuntimeDecodeTiming165 <full|runtime> <input.json>")
  let some path := args.tail?.bind List.head? | throw (IO.userError "usage: RuntimeDecodeTiming165 <full|runtime> <input.json>")
  let text ← IO.FS.readFile path
  let start ← IO.monoNanosNow
  let (obligationCount, ready) ← match mode with
    | "full" =>
      match decodeJson text with
      | .error error => throw (IO.userError s!"full decoder error: {error}")
      | .ok result => pure (result.blockingObligations.size, result.executionInput.isSome)
    | "runtime" =>
      match decodeRuntimeJson text with
      | .error error => throw (IO.userError s!"runtime decoder error: {error}")
      | .ok result => pure (result.blockingObligations.size, result.executionInput.isSome)
    | _ => throw (IO.userError s!"unknown decoder mode `{mode}`")
  let stop ← IO.monoNanosNow
  IO.println s!"mode={mode} elapsed_ns={stop - start} obligations={obligationCount} ready={ready}"
