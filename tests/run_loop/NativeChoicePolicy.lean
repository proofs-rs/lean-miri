import Miri.Input.ExecutionChoicePolicy

open Miri Miri.Interpreter

private def access : ExecutionChoices.Access ExecutionChoices.Tape := ⟨id, fun _ tape => tape⟩

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def exercise (tape : ExecutionChoices.Tape) : IO Unit := do
  let draws : EStateM StepError ExecutionChoices.Tape Unit := do
    for _ in [:65537] do
      let _ ← ExecutionChoices.index access .scheduler 3
    let bytes ← ExecutionChoices.bytes access .osRandom 8192
    unless bytes.size == 8192 do throw (.invalidProgram "wrong byte length")
  match draws.run tape with
  | .error error _ => throw (IO.userError s!"unbounded generation failed: {reprStr error}")
  | .ok _ after =>
    check (after.cursor == 65538 && after.generatedChoices == 65538 && after.events.size == 65538)
      "unbounded generation lost a choice or event"

def main : IO Unit := do
  exercise (Input.ExecutionChoicePolicy.unboundedDiagnosticTape)
  exercise (Input.ExecutionChoicePolicy.unboundedSeededDiagnosticTape 42)
  let bounded := Input.ExecutionChoicePolicy.diagnosticTape 1 4096
  match (do
    let _ ← ExecutionChoices.index access .scheduler 3
    ExecutionChoices.index access .scheduler 3).run bounded with
  | .error (.resourceExhaustion _) tape => check (tape.cursor == 1) "bounded draw changed"
  | _ => throw (IO.userError "bounded draw cap was not retained")
  match (ExecutionChoices.bytes access .osRandom 4097).run bounded with
  | .error (.resourceExhaustion _) tape => check (tape.cursor == 0) "bounded byte cap changed"
  | _ => throw (IO.userError "bounded byte cap was not retained")
  let malformed := Input.ExecutionChoicePolicy.unboundedDiagnosticTape #[.index .addressSlack 0]
  match (ExecutionChoices.index access .scheduler 3).run malformed with
  | .error (.callback _) tape => check (tape.cursor == 0) "malformed prefix was consumed"
  | _ => throw (IO.userError "malformed prefix bypassed validation")
  IO.println "native choice policies: passed"
