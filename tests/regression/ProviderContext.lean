import Miri.Input.Decoder
import Miri.Input.LowerMIR
import Miri.Input.CompilerProviders

open Miri Input

private def must {α : Type} (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error reason => throw (IO.userError reason)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let [firstPath, secondPath] := args
    | throw (IO.userError "usage: ProviderContextTests <root-u32> <control-flow>")
  let first ← must (decodeJson (← IO.FS.readFile firstPath))
  let second ← must (decodeJson (← IO.FS.readFile secondPath))
  let firstProgram ← must (lowerProgram first.document)
  let secondProgram ← must (lowerProgram second.document)
  check (firstProgram.input.raw != secondProgram.input.raw)
    "two distinct genuine documents unexpectedly equal"
  let prepared ← must (CompilerProviders.prepare firstProgram)
  check (prepared.runtime.source.raw == firstProgram.input.raw)
    "provider runtime does not use its owner source"
  let nested := prepared.lifecycle.calls.symbols.facts.context
  let updated := nested.withProgram secondProgram
  check (updated.runtime.source.raw == nested.runtime.source.raw &&
      updated.program.input.raw == nested.program.input.raw)
    "replacing the lowered view changed its source owner"
  check (updated.program.bundle.bodies.size == secondProgram.bundle.bodies.size)
    "replacing lowered tables did not update the body view"
  let independent ← must (CompilerFacts.ofProgram secondProgram)
  check (independent.runtime.source.raw == secondProgram.input.raw)
    "independent source owner did not retain its input"
  IO.println "single source provider owner PASS"
