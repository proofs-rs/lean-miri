import Miri.Input.Decoder
import Miri.Input.LowerMIR

open Lean Miri.Input

private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error e => throw (IO.userError e)

private def same (a b : Except String TypedValue) : Bool :=
  match a, b with
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

private def checkBody (document : ImportDocumentCore) (body : BodyCore) : IO Unit := do
  for (block, blockIndex) in body.blocks.toList.zipIdx do
    let mut nodes := block.statements.mapIdx fun index node =>
      (s!"{body.sourcePath}.basic_blocks[{blockIndex}].statements[{index}].kind", node.value)
    nodes := nodes.push (s!"{body.sourcePath}.basic_blocks[{blockIndex}].terminator.kind", block.terminator.value)
    for (path, _) in nodes do
      let some raw := jsonAtPath document.raw path |
        throw (IO.userError s!"missing original MIR {path}")
      unless same (decodeCompilerValue raw) (decodeCompilerValueAtPath raw path document.compilerValueMemo) do
        throw (IO.userError s!"cached source decode differs {path}")
      let changed := Json.mkObj [("status", .str "unsupported"), ("kind", .str "synthetic_unknown")]
      unless same (decodeCompilerValue changed) (decodeCompilerValueAtPath changed path document.compilerValueMemo) do
        throw (IO.userError s!"changed source inherited cached decode {path}")

private def checkOne (referenceDirectory path : String) : IO Unit := do
  let text ← IO.FS.readFile path
  let name := (System.FilePath.mk path).fileName.getD path
  let reference ← IO.FS.readFile (System.FilePath.mk referenceDirectory / name)
  -- The reference image reader deliberately gets no root ID and must take
  -- the ordinary typed parser, independently of the indexed MIR memo.
  match decodeRuntimeJson text, decodeRuntimeJsonReference text with
  | .error a, .error b =>
    unless a == b do throw (IO.userError s!"uncached image diagnostic changed {path}")
  | .ok a, .ok b =>
    unless a.blockingObligations == b.blockingObligations &&
        a.document.obligations == b.document.obligations &&
        a.executionInput.isSome == b.executionInput.isSome do
      throw (IO.userError s!"uncached image readiness differs {path}")
  | _, _ => throw (IO.userError s!"uncached image result class differs {path}")
  match decodeRuntimeJson text, decodeRuntimeJsonReference reference with
  | .error a, .error b =>
    unless a == b do throw (IO.userError s!"first diagnostic changed {path}: {a} / {b}")
  | .ok a, .ok b =>
    unless a.blockingObligations == b.blockingObligations &&
        a.executionInput.isSome == b.executionInput.isSome &&
        a.document.obligations == b.document.obligations do
      throw (IO.userError s!"readiness/ordered obligations differ {path}")
    let mut bodiesA := a.document.bodies.map (·.toBodyCore)
    let mut bodiesB := b.document.bodies.map (·.toBodyCore)
    for inst in a.document.instances do
      if let some body := inst.body then bodiesA := bodiesA.push body.toBodyCore
    for inst in b.document.instances do
      if let some body := inst.body then bodiesB := bodiesB.push body.toBodyCore
    unless bodiesA.size == bodiesB.size do throw (IO.userError "body count differs")
    for (left, right) in bodiesA.zip bodiesB do
      unless left.blocks.size == right.blocks.size do throw (IO.userError "block count differs")
      for (l, r) in left.blocks.zip right.blocks do
        unless l.statements.map (·.value) == r.statements.map (·.value) &&
            l.terminator.value == r.terminator.value do
          throw (IO.userError s!"typed MIR differs {left.sourcePath}")
      checkBody a.document left
  | _, _ => throw (IO.userError s!"decoder result class differs {path}")

def main (args : List String) : IO Unit := do
  let reference :: paths := args | throw (IO.userError "expected reference directory and prepared image cases")
  unless !paths.isEmpty do throw (IO.userError "expected prepared image cases")
  for path in paths do checkOne reference path
  IO.println s!"indexed typed MIR, source-binding fallback, readiness and ordered diagnostics: PASS ({paths.length} cases)"
