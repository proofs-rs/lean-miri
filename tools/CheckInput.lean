import Miri.Input.Decoder

/-! Check external input acceptance without executing MIR or proving safety. -/
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
      IO.println s!"{path}: input=rejected; decode_error={error}; safety=not_evaluated"
    | .ok _ =>
      IO.println s!"{path}: input=accepted; safety=not_evaluated"
  return if readyEverywhere then 0 else 2
