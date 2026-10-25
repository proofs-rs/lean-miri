import Miri.Input.Decoder

/-! Diagnostic-only checker for large fresh imports. It reports the exact
decoder readiness blockers; it does not modify or reinterpret readiness. -/
open Miri.Input

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    throw (IO.userError "usage: check_input <export.json> [...]")
  let mut readyEverywhere := true
  for path in args do
    let source ← IO.FS.readFile path
    match decodeJson source with
    | .error error =>
      readyEverywhere := false
      IO.println s!"{path}: decode_error={error}; structural_readiness=unavailable; safety=not_evaluated"
    | .ok decoded =>
      let ready := decoded.executionInput.isSome
      readyEverywhere := readyEverywhere && ready
      IO.println s!"{path}: structural_readiness={if ready then "ready" else "unavailable"} total_obligations={decoded.document.obligations.size} blocking_obligations={decoded.blockingObligations.size} safety=not_evaluated"
      for (issue, index) in decoded.blockingObligations.toList.zipIdx do
        IO.println s!"blocking[{index}]: {issue.path}: {issue.message}"
  return if readyEverywhere then 0 else 2
