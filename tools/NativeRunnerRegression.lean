import Miri.Input.NativeRunnerOptions
import Miri.Interpreter.NativeRunLoop
import Miri.Input.ExecutionChoicePolicy
import Miri.Input.DecoderValues
import Miri.Input.CompilerBodyEquality

open Lean Miri.Interpreter Miri.Input

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def lateStep (_iteration state : Nat) : StepResult Nat Unit :=
  if state == 100001 then (state + 1, .error (.undefinedBehavior "late UB"))
  else (state + 1, .ok ())

def main : IO Unit := do
  match NativeRunLoop.run lateStep (some 100000) 0 with
  | .exhausted state count => check (state == 100000 && count == 100000) "bounded prefix state"
  | _ => throw (IO.userError "bound fabricated termination")
  match NativeRunLoop.run lateStep none 0 with
  | .stopped state (.undefinedBehavior "late UB") count =>
    check (state == 100002 && count == 100002) "unbounded late UB state"
  | _ => throw (IO.userError "late UB was hidden")
  match NativeRunLoop.run (fun _ (state : Nat) =>
      (state + 1, .error (.termination (.exit 7 true)))) none 0 with
  | .stopped 1 (.termination (.exit 7 true)) 1 => pure ()
  | _ => throw (IO.userError "exit state or code changed")
  check ((Miri.NativeRunnerOptions.iterationLimit ["file", "--max-iterations", "12", "--profile"]).toOption ==
    some (["file", "--profile"], some 12)) "iteration option order"
  for args in [["--max-iterations"], ["--max-iterations", "-1"],
      ["--max-iterations", "1", "--max-iterations", "2"]] do
    check (!(Miri.NativeRunnerOptions.iterationLimit args).isOk) "invalid option accepted"
  for seed in [none, some 0, some 123] do
    let mut tape := ExecutionChoicePolicy.generatedTape seed
    let bounded := match seed with
      | none => ExecutionChoicePolicy.diagnosticTape 65536 4096
      | some seed => ExecutionChoicePolicy.seededDiagnosticTape 65536 4096 seed
    let mut reference := bounded
    for _ in [:16] do
      let cursor := tape.cursor
      match ExecutionChoices.index ⟨id, fun _ value => value⟩ .scheduler 7 tape with
      | .ok value next =>
        if cursor < 65536 then
          match ExecutionChoices.index ⟨id, fun _ value => value⟩ .scheduler 7 reference with
          | .ok other nextRef =>
            check (value == other) "seeded trace changed"
            reference := nextRef
          | _ => throw (IO.userError "reference prefix failed")
        tape := next
      | _ => throw (IO.userError "implicit choice quota remains")
    -- A full supplied history at the old quota boundary, with the same live
    -- RNG state and validated event shape. Only the next request is executed.
    tape := {tape with inputs := Array.replicate 65536 (.index .scheduler 0), cursor := 65536, generatedChoices := 65536, events := Array.replicate 65536 ⟨.index .scheduler 7, .index .scheduler 0⟩}
    match ExecutionChoices.index ⟨id, fun _ value => value⟩ .scheduler 7 tape with
    | .ok _ next => tape := next
    | _ => throw (IO.userError "implicit choice quota remains")
    check (tape.cursor == 65537 && tape.events.size == 65537) "choice recording lost"
    match ExecutionChoices.bytes ⟨id, fun _ value => value⟩ .osRandom 4097 tape with
    | .ok bytes next => check (bytes.size == 4097 && next.cursor == 65538) "byte request truncated"
    | _ => throw (IO.userError "implicit byte quota remains")
    let bad := ExecutionChoicePolicy.generatedTape seed #[.index .scheduler 7]
    match ExecutionChoices.index ⟨id, fun _ value => value⟩ .scheduler 7 bad with
    | .error _ after => check (after.cursor == 0 && after.generatedChoices == 0) "bad supplied head generated fallback"
    | _ => throw (IO.userError "out-of-domain head accepted")
  let body : Miri.MIR.Body := ⟨.Built, 0, none, #[0, 1], #[]⟩
  check (bodyContentsEqual body body) "same canonical body rejected"
  let equalBody : Miri.MIR.Body := ⟨.Built, 0, none, (List.range 2).toArray, #[]⟩
  check (bodyContentsEqual body equalBody) "equal separately built body rejected"
  for changed in [{body with argumentCount := 1}, {body with locals := #[1, 0]},
      {body with spreadArgument := some 0}] do
    check (!(bodyContentsEqual body changed)) "mismatched canonical body accepted"
  for value in [Json.null, .num 3, .arr #[], .str "text",
      Json.mkObj [], Json.mkObj [("type_id", toJson (3 : Nat))],
      .obj ⟨⟨.inner 999 "type_id" (toJson (3 : Nat)) .leaf .leaf⟩⟩,
      .obj ⟨⟨.inner 1 "type_id" (toJson (3 : Nat))
        (.inner 0 "a" Json.null .leaf .leaf) .leaf⟩⟩,
      Json.mkObj [("type_id", .str "bad")],
      Json.mkObj [("type_id", toJson (3 : Nat)), ("x", Json.null)]] do
    for key in ["type_id", "missing"] do
      check (DecoderValues.singletonRef value key == DecoderValues.singletonRefReference value key)
        "singleton reference shape changed"
      check (DecoderValues.optionalStringValue value key == (value.getObjValAs? String key).toOption)
        "optional string changed"
  IO.println "native runner regression: PASS"
