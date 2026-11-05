import Miri.Input.DecoderValues

open Lean Miri.Input

private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)

private def checkOne (path : System.FilePath) : IO Unit := do
  let input ← must (Json.parse (← IO.FS.readFile path))
  let (graph, node) ← must (JsonTraversalCache.resolve input)
  unless node.audit do throw (IO.userError s!"{path}: node/hash/runtime summary audit failed")
  let fast := DecoderValues.decodeRuntimeValue node "$"
  let reference := DecoderValues.decodeRuntimeValue (.uncached graph.root) "$"
  match fast, reference with
  | .error left, .error right =>
    unless left == right do throw (IO.userError s!"{path}: first error changed: {left} / {right}")
  | .ok left, .ok right =>
    unless left.summary == right.summary &&
        DecoderValues.flattenRuntimeObligations left.obligations ==
          DecoderValues.flattenRuntimeObligations right.obligations do
      throw (IO.userError s!"{path}: summary or ordered obligations changed")
    if !node.mayHaveRuntimeChecks then
      unless (DecoderValues.flattenRuntimeObligations right.obligations).isEmpty do
        throw (IO.userError s!"{path}: claimed inert root retains obligations")
  | _, _ => throw (IO.userError s!"{path}: runtime result class changed")

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected runtime-summary fixture directory")
  let entries ← (System.FilePath.mk directory).readDir
  let mut count := 0
  for entry in entries do
    if entry.path.extension == some "json" then
      checkOne entry.path
      count := count + 1
  unless count > 1000 do throw (IO.userError "runtime-summary fixture set is incomplete")
  IO.println s!"runtime summary: exact result, ordered diagnostics, HIR/context retention and inert-branch checks PASS ({count} cases)"
