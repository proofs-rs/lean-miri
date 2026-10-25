import Miri.Input

open Lean
open Miri.Input

private def fail (message : String) : IO α := throw (IO.userError message)

def main (args : List String) : IO UInt32 := do
  let path ← match args with
    | value :: _ => pure value
    | [] => fail "usage: SelectedScopeTests <rooted-schema-v3-export.json>"
  let source ← IO.FS.readFile path
  let result ← match decodeJson source with
    | .ok value => pure value
    | .error error => fail s!"rooted compiler graph was rejected: {error}"
  if result.document.completenessStatus != .incomplete then
    fail "rooted export must retain the independent document-wide incomplete status"
  if result.document.selectedScope.isNone then
    fail "rooted export did not retain selected_scope metadata"
  if result.executionInput.isNone then
    fail "fully checked selected structural closure did not produce scoped ExecutionInput"
  if result.document.obligations.isEmpty then
    fail "scoped import discarded global completeness obligations"
  match result.document.selectedScope with
  | none => fail "selected_scope disappeared after successful check"
  | some scope =>
    if scope.statusText != "complete" || scope.roots.isEmpty || !scope.unresolvedObligations.isEmpty then
      fail "selected_scope metadata does not describe a closed root graph"
  IO.println s!"selected scope decoded: bodies={result.document.bodies.size}, types={result.document.types.size}, allocations={result.document.allocations.size}"
  return 0
