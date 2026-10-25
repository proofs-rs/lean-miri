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
  check (prepared.loweringContext.sourceDocument == some firstProgram.input.raw)
    "prepared provider cache does not point at own program"
  let nested := prepared.lifecycle.calls.symbols.facts.context
  let wrongNested : CompilerFacts.Context := { nested with
    program := secondProgram, lowering := none }
  check (wrongNested.loweringContext.sourceDocument == some secondProgram.input.raw)
    "manual nested facts context did not preserve fallback source"
  let wrongFacts := { prepared.lifecycle.calls.symbols.facts with context := wrongNested }
  let wrongSymbols := { prepared.lifecycle.calls.symbols with facts := wrongFacts }
  let wrongCalls := { prepared.lifecycle.calls with symbols := wrongSymbols }
  let wrongLifecycle := { prepared.lifecycle with calls := wrongCalls }
  let manualProvider := { prepared with lifecycle := wrongLifecycle, lowering := none }
  check (manualProvider.loweringContext.sourceDocument == some firstProgram.input.raw)
    "manual provider incorrectly followed its mismatched nested context"
  check (manualProvider.lifecycle.calls.symbols.facts.context.loweringContext.sourceDocument ==
    some secondProgram.input.raw)
    "mismatched nested context unexpectedly changed"
  let rebound := wrongNested.withProgram firstProgram
  check (rebound.loweringContext.sourceDocument == some firstProgram.input.raw)
    "withProgram left a stale context certificate"
  IO.println "source147 provider-own-program and nested-context fallback PASS"
