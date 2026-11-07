import MiriTests.Input.ReferenceDecoder
import Miri.Input.LowerMIR
open Lean Miri.Input
private def must (x : Except String α) : IO α :=
  match x with | .ok x => pure x | .error e => throw (IO.userError e)
def main (args : List String) : IO Unit := do
  for file in args do
    let source ← IO.FS.readFile file
    let catalog ← must (Reader.Catalog.parse (← must (Json.parse source)))
    let actual ← must (decodeRuntimeJson source)
    unless actual.document.raw == catalog.root && actual.document.sharedNodes == catalog.nodes do
      throw (IO.userError s!"transport JSON was expanded: {file}")
    let expected ← must (decodeRuntimeJsonReference source)
    unless actual.executionInput.isSome == expected.executionInput.isSome do
      throw (IO.userError s!"readiness changed: {file}")
    unless actual.document.obligations == expected.document.obligations do
      IO.println s!"actual: {repr actual.document.obligations}"
      IO.println s!"oracle: {repr expected.document.obligations}"
      throw (IO.userError s!"obligations changed: {file}")
    unless actual.document.mirTables == expected.document.mirTables do
      throw (IO.userError s!"typed MIR changed: {file}")
    let actualProgram ← must (lowerCoreProgram actual.document)
    let expectedProgram ← must (lowerCoreProgram expected.document)
    for body in actualProgram.bundle.bodies do
      unless body.input.syntaxObligations.isSome do
        throw (IO.userError "runtime source syntax was retained")
      for block in body.input.blocks do
        for node in block.statements.push block.terminator do
          match node.value with
          | .diagnostic .null => pure ()
          | _ => throw (IO.userError "runtime source AST was expanded")
    unless actualProgram.bundle.bodies.map (·.obligations) == expectedProgram.bundle.bodies.map (·.obligations) do
      throw (IO.userError s!"source syntax obligations changed: {file}")
    IO.println s!"unexpanded transport semantics: PASS {file}"
