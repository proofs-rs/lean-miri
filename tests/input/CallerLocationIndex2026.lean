import MiriTests.Input.LegacyFixture
import Miri.Input.EvalPreparation
import Miri.Input.CompilerValueConstants

open Lean Miri.Input Miri.Interpreter

private def must (value : Except String α) : IO α :=
  match value with | .ok x => pure x | .error e => throw (IO.userError e)

private def withRows (p : CompilerProviders.Prepared) (rows : Array Catalog.CallerLocation) :
    CompilerProviders.Prepared :=
  let queries := {p.program.input.queries with callerLocations := rows}
  {p with program := {p.program with input := {p.program.input with queries}}, lowering := none}

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected ordinary export fixture")
  let decoded ← must (decodeFixture (← IO.FS.readFile path))
  let program ← must (lowerProgram decoded.document)
  let p := (← must (EvalPreparation.prepare program).outcome).compiler
  let some source := p.program.input.queries.callerLocations[0]? |
    throw (IO.userError "fixture has no caller-location rows")
  let row := {source with span := 0}
  let span : Miri.MIR.SpanRef := ⟨0⟩
  let expected ← must (CompilerValueConstants.callerLocation (withRows p #[row]) span)
  let duplicate ← must (CompilerValueConstants.callerLocation (withRows p #[row,row]) span)
  check (decide (duplicate = expected)) "duplicate caller-location row changed result"
  let some resultType := row.resultType | throw (IO.userError "caller result type absent")
  let typeName : Catalog.TypeName := ⟨resultType, resultType, row.value⟩
  let queries := {p.program.input.queries with typeNames := #[typeName]}
  let typeNameProvider := {p with program := {p.program with input := {p.program.input with queries}}, lowering := none}
  check (decide ((← must (CompilerValueConstants.typeName typeNameProvider resultType)) = expected))
    "type-name and caller-location constant paths disagree"
  let conflict := {row with resultType := none}
  check (!(CompilerValueConstants.callerLocation (withRows p #[row, conflict]) span).isOk)
    "conflicting caller-location rows were accepted"
  check (!(CompilerValueConstants.callerLocation (withRows p #[]) span).isOk)
    "missing caller-location row was accepted"
  check (!(CompilerValueConstants.callerLocation (withRows p #[conflict]) span).isOk)
    "missing caller-location type was accepted"
  let other := {row with span := 1}
  let selected ← must (CompilerValueConstants.callerLocation (withRows p #[other,row]) span)
  check (decide (selected = expected)) "caller-location selected a different span identity"
  check (!(CompilerValueConstants.callerLocation (withRows p #[row])
    ⟨p.program.compilerTables.spans.size⟩).isOk) "out-of-bounds source span was accepted"
  IO.println "typed caller-location IDs, duplicates, conflicts, missing types and span bounds: PASS"
