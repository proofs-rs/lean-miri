import Miri.Input

open Lean
open Miri.Input

private def fail (message : String) : IO α := throw (IO.userError message)

private partial def hasCoverage (value : TypedValue) : Bool :=
  match value with
  | .enumTag .coverageKind tag _ =>
    tag.status == .supported &&
      (tag.tag == "point" || tag.tag == "block_marker" || tag.tag == "virtual_counter")
  | .array values => values.any hasCoverage
  | .object fields => fields.any fun (_, child) => hasCoverage child
  | .statement _ _ fields | .terminator _ _ fields | .rvalue _ _ fields
  | .operand _ _ fields | .projection _ fields | .enumTag _ _ fields =>
    fields.any fun (_, child) => hasCoverage child
  | _ => false

def main (args : List String) : IO UInt32 := do
  let path ← match args with
    | value :: _ => pure value
    | [] => fail "usage: NoopTests <rooted-coverage-export.json>"
  let source ← IO.FS.readFile path
  let result ← match decodeJson source with
    | .ok value => pure value
    | .error error => fail s!"valid rooted coverage export rejected: {error}"
  if result.executionInput.isNone then
    fail "complete rooted no-op statements did not produce structural input"
  if !hasCoverage result.document.typedTree then
    fail "Coverage payload was not decoded to a typed coverage tag"
  IO.println "typed rooted Coverage payload accepted as structural input"
  return 0
