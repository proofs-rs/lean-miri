import MiriTests.Input.LegacyFixture
import Miri.Input.EvalPreparation

open Miri Miri.Input Miri.Interpreter

private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected genuine tuple-unsizing export")
  let decoded ← must (decodeFixture (← IO.FS.readFile path))
  let program ← must (lowerProgram decoded.document)
  let prepared ← must (EvalPreparation.prepare program).outcome
  let facts := prepared.compiler.lifecycle.calls.symbols.facts
  let mut tuples := 0
  let mut unsupported := 0
  for node in prepared.compiler.program.input.types do
    match node.shape with
    | .tuple elements =>
      let actual ← must (CompilerFactAdapters.castTypeInfo facts node.id)
      unless actual == .tuple elements do throw (IO.userError "tuple fields lost during cast classification")
      tuples := tuples + 1
    | .never =>
      unless !(CompilerFactAdapters.castTypeInfo facts node.id).isOk do
        throw (IO.userError "unrelated unsupported cast kind became accepted")
      unsupported := unsupported + 1
    | _ => pure ()
  unless tuples > 0 && unsupported > 0 do throw (IO.userError "missing tuple/unsupported controls")
  IO.println s!"PASS exact tuple cast fields ({tuples}) and unsupported-kind negatives ({unsupported})"
