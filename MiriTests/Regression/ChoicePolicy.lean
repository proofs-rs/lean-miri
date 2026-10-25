import Miri.Input.ExecutionChoicePolicy

open Miri.Interpreter
open Miri.Interpreter.ExecutionChoices
open Miri.Input.ExecutionChoicePolicy

abbrev ChoiceM := EStateM StepError

def tapeAccess : ExecutionChoices.Access ExecutionChoices.Tape :=
  ⟨id, fun _ tape => tape⟩

def check (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def expectCallback (error : StepError) : Bool :=
  match error with | .callback _ => true | _ => false

def expectInvalidProgram (error : StepError) : Bool :=
  match error with | .invalidProgram _ => true | _ => false

def expectResourceExhaustion (error : StepError) : Bool :=
  match error with | .resourceExhaustion _ => true | _ => false

def strictExhaustion : IO Unit := do
  let initial := strictTape
  match (ExecutionChoices.boolean tapeAccess .floatEqual).run initial with
  | .error error final =>
    check (expectCallback error) "strict exhaustion must keep callback/unknown-choice classification"
    check (final.cursor == 0 && final.generatedChoices == 0 && final.events.isEmpty && final.inputs.isEmpty)
      "strict exhaustion mutated the tape"
  | .ok _ _ => throw (IO.userError "strict exhausted tape unexpectedly succeeded")

def strictTranscript : IO Unit := do
  let initial := strictTape #[.boolean .floatEqual true]
  match (ExecutionChoices.boolean tapeAccess .floatEqual).run initial with
  | .error error _ => throw (IO.userError s!"strict valid choice failed: {repr error}")
  | .ok value final => do
    check value "strict Boolean returned wrong value"
    check (final.cursor == 1 && final.generatedChoices == 0 && final.events.size == 1)
      "strict Boolean did not consume exactly one entry and append one event"
    match final.events[0]? with
    | some event =>
      match event.request with
      | .boolean .floatEqual => pure ()
      | _ => throw (IO.userError "strict event request mismatch")
      match event.input with
      | .boolean .floatEqual true => pure ()
      | _ => throw (IO.userError "strict event did not retain exact supplied input")
    | none => throw (IO.userError "strict transcript event missing")

def malformedDiagnosticInput : IO Unit := do
  let initial := diagnosticTape 4 8 #[.boolean .floatFuse true]
  match (ExecutionChoices.boolean tapeAccess .floatEqual).run initial with
  | .error error final => do
    check (expectCallback error) "malformed supplied input should be callback/unknown, not generated"
    check (final.cursor == 0 && final.generatedChoices == 0 && final.events.isEmpty && final.inputs.size == 1)
      "malformed supplied input mutated cursor, generation count, transcript, or prefix"
    match final.inputs[0]? with
    | some (.boolean .floatFuse true) => pure ()
    | _ => throw (IO.userError "malformed diagnostic input prefix changed")
  | .ok _ _ => throw (IO.userError "malformed supplied input unexpectedly succeeded")

def malformedStrictInput : IO Unit := do
  let initial := strictTape #[.boolean .floatFuse true]
  match (ExecutionChoices.boolean tapeAccess .floatEqual).run initial with
  | .error error final => do
    check (expectCallback error) "strict wrong-site input should remain callback/unknown"
    check (final.cursor == 0 && final.generatedChoices == 0 && final.events.isEmpty && final.inputs.size == 1)
      "strict malformed input mutated tape"
    match final.inputs[0]? with
    | some (.boolean .floatFuse true) => pure ()
    | _ => throw (IO.userError "strict malformed input prefix changed")
  | .ok _ _ => throw (IO.userError "strict wrong-site input unexpectedly succeeded")

def emptyDomainsBeforeBudget : IO Unit := do
  let initial := diagnosticTape 0 0
  match (ExecutionChoices.index tapeAccess .scheduler 0).run initial with
  | .error error final => do
    check (expectInvalidProgram error) "empty index support should fail before diagnostic budget"
    check (final.cursor == 0 && final.generatedChoices == 0 && final.events.isEmpty)
      "empty index support mutated tape"
  | .ok _ _ => throw (IO.userError "empty index support unexpectedly succeeded")
  match (ExecutionChoices.integer tapeAccess .floatUlp 4 3).run initial with
  | .error error final => do
    check (expectInvalidProgram error) "empty integer support should fail before diagnostic budget"
    check (final.cursor == 0 && final.generatedChoices == 0 && final.events.isEmpty)
      "empty integer support mutated tape"
  | .ok _ _ => throw (IO.userError "empty integer support unexpectedly succeeded")

def bernoulliOutcomes : IO Unit := do
  let zero := 0
  let one := 0x3ff0000000000000
  let half := 0x3fe0000000000000
  match (ExecutionChoices.bernoulli tapeAccess .preemption zero).run (diagnosticTape 1 0) with
  | .error error _ => throw (IO.userError s!"zero-rate diagnostic failed: {repr error}")
  | .ok value final => do
    check (!value && final.generatedChoices == 1 && final.cursor == 1)
      "zero Bernoulli endpoint must generate false and consume it"
    match final.events[0]? with
    | some event =>
      match event.request with
      | .bernoulli .preemption 0 => pure ()
      | _ => throw (IO.userError "zero endpoint request transcript mismatch")
      match event.input with
      | .boolean .preemption false => pure ()
      | _ => throw (IO.userError "zero endpoint transcript input mismatch")
    | none => throw (IO.userError "zero endpoint transcript missing")
  match (ExecutionChoices.bernoulli tapeAccess .preemption one).run (diagnosticTape 1 0) with
  | .error error _ => throw (IO.userError s!"one-rate diagnostic failed: {repr error}")
  | .ok value final => do
    check (value && final.generatedChoices == 1 && final.cursor == 1)
      "one Bernoulli endpoint must generate true and consume it"
    match final.events[0]? with
    | some event =>
      match event.request with
      | .bernoulli .preemption 0x3ff0000000000000 => pure ()
      | _ => throw (IO.userError "one endpoint request transcript mismatch")
      match event.input with
      | .boolean .preemption true => pure ()
      | _ => throw (IO.userError "one endpoint transcript input mismatch")
    | none => throw (IO.userError "one endpoint transcript missing")
  match (ExecutionChoices.bernoulli tapeAccess .preemption half).run
      (strictTape #[.boolean .preemption false]) with
  | .error error _ => throw (IO.userError s!"interior false Bernoulli outcome rejected: {repr error}")
  | .ok value final => do
    check (!value && final.cursor == 1 && final.events.size == 1)
      "interior Bernoulli false should be permitted and consumed"
    match final.events[0]? with
    | some event =>
      match event.request with
      | .bernoulli .preemption 0x3fe0000000000000 => pure ()
      | _ => throw (IO.userError "interior request transcript mismatch")
    | none => throw (IO.userError "interior Bernoulli transcript missing")

def invalidProbabilityBeforeDemand : IO Unit := do
  let nan := 0x7ff8000000000000
  let initial := diagnosticTape 3 0
  match (ExecutionChoices.bernoulli tapeAccess .preemption nan).run initial with
  | .error error final => do
    check (expectInvalidProgram error) "NaN probability must be rejected as invalid program"
    check (final.cursor == 0 && final.generatedChoices == 0 && final.events.isEmpty && final.inputs.isEmpty)
      "invalid probability inspected/generated/consumed tape input"
  | .ok _ _ => throw (IO.userError "NaN Bernoulli rate unexpectedly succeeded")

def indexUsesExactCount : IO Unit := do
  let initial := strictTape #[.index .scheduler 2]
  match (ExecutionChoices.index tapeAccess .scheduler 3).run initial with
  | .error error _ => throw (IO.userError s!"index within exact support rejected: {repr error}")
  | .ok value final => do
    check (value == 2 && final.cursor == 1 && final.events.size == 1)
      "index choice did not return/consume valid source value"
    match final.events[0]? with
    | some event =>
      match event.request with
      | .index .scheduler 3 => pure ()
      | _ => throw (IO.userError "index transcript did not retain exact source count")
      match event.input with
      | .index .scheduler 2 => pure ()
      | _ => throw (IO.userError "index transcript input mismatch")
    | none => throw (IO.userError "index transcript missing")

def integerLowerBoundary : IO Unit := do
  match (ExecutionChoices.integer tapeAccess .floatUlp (-4) 5).run (diagnosticTape 1 0) with
  | .error error _ => throw (IO.userError s!"bounded integer choice failed: {repr error}")
  | .ok value final => do
    check (value == -4 && final.cursor == 1 && final.generatedChoices == 1 && final.events.size == 1)
      "diagnostic integer did not choose lower boundary"
    match final.events[0]? with
    | some event =>
      match event.request with
      | .integer .floatUlp (-4) 5 => pure ()
      | _ => throw (IO.userError "integer transcript bounds mismatch")
      match event.input with
      | .integer .floatUlp (-4) => pure ()
      | _ => throw (IO.userError "integer transcript input mismatch")
    | none => throw (IO.userError "integer transcript missing")

def bytesBudgetAndExactLength : IO Unit := do
  match (ExecutionChoices.bytes tapeAccess .osRandom 3).run (diagnosticTape 1 3) with
  | .error error _ => throw (IO.userError s!"exact byte-budget choice failed: {repr error}")
  | .ok bytes final => do
    check (bytes.size == 3 && bytes.data.all (· == 0)) "diagnostic bytes must be exact length and zero-filled"
    check (final.cursor == 1 && final.generatedChoices == 1 && final.events.size == 1)
      "byte vector should count as one generated choice and one event"
    match final.events[0]? with
    | some event =>
      match event.request with
      | .bytes .osRandom 3 => pure ()
      | _ => throw (IO.userError "byte transcript request length mismatch")
      match event.input with
      | .bytes .osRandom values =>
        check (values.size == 3 && values.all (· == 0)) "byte transcript did not preserve exact generated vector"
      | _ => throw (IO.userError "byte transcript input mismatch")
    | none => throw (IO.userError "byte transcript missing")
  let capped := diagnosticTape 2 2
  match (ExecutionChoices.bytes tapeAccess .osRandom 3).run capped with
  | .error error final => do
    check (expectResourceExhaustion error) "byte-length cap should be resource exhaustion"
    check (final.cursor == 0 && final.generatedChoices == 0 && final.events.isEmpty && final.inputs.isEmpty)
      "over-cap byte request mutated tape"
  | .ok _ _ => throw (IO.userError "over-cap byte vector unexpectedly succeeded")
  let malformed := diagnosticTape 2 8 #[.bytes .osRandom #[1,2]]
  match (ExecutionChoices.bytes tapeAccess .osRandom 3).run malformed with
  | .error error final => do
    check (expectCallback error) "supplied wrong-length bytes should be malformed callback input"
    check (final.cursor == 0 && final.generatedChoices == 0 && final.events.isEmpty && final.inputs.size == 1)
      "wrong-length supplied bytes fell back or mutated tape"
    match final.inputs[0]? with
    | some (ExecutionChoices.Input.bytes .osRandom values) =>
      check (values.size == 2 && values[0]? == some 1 && values[1]? == some 2)
        "malformed byte prefix changed"
    | _ => throw (IO.userError "malformed byte input prefix changed")
  | .ok _ _ => throw (IO.userError "wrong-length supplied bytes unexpectedly succeeded")

def diagnosticCursorGuard : IO Unit := do
  let initial : ExecutionChoices.Tape := { (diagnosticTape 4 0) with cursor := 1 }
  match (ExecutionChoices.boolean tapeAccess .floatEqual).run initial with
  | .error error final => do
    check (expectInvalidProgram error) "diagnostic cursor beyond prefix must be invalid program"
    check (final.cursor == 1 && final.generatedChoices == 0 && final.events.isEmpty && final.inputs.isEmpty)
      "diagnostic cursor guard mutated tape"
  | .ok _ _ => throw (IO.userError "diagnostic cursor beyond prefix unexpectedly generated")

def twoBooleans : ChoiceM ExecutionChoices.Tape (Bool × Bool) := do
  let first ← ExecutionChoices.boolean tapeAccess .floatEqual
  let second ← ExecutionChoices.boolean tapeAccess .floatEqual
  pure (first,second)

def transcriptFreshness : IO Unit := do
  let initial := strictTape #[.boolean .floatEqual false, .boolean .floatEqual true]
  match twoBooleans.run initial with
  | .error error _ => throw (IO.userError s!"two supplied choices failed: {repr error}")
  | .ok (first,second) final => do
    check (!first && second && final.cursor == 2 && final.generatedChoices == 0 && final.events.size == 2)
      "two reached source draws did not consume distinct tape entries"
    match final.events[0]?, final.events[1]? with
    | some a, some b =>
      check ((match a.request with | .boolean .floatEqual => true | _ => false) && (match b.request with | .boolean .floatEqual => true | _ => false))
        "repeated source calls lost exact request identity"
      match a.input, b.input with
      | .boolean .floatEqual false, .boolean .floatEqual true => pure ()
      | _, _ => throw (IO.userError "repeated calls reused or reordered supplied inputs")
    | _, _ => throw (IO.userError "two-call transcript is incomplete")

def generatedChoiceBudget : IO Unit := do
  let initial := diagnosticTape 1 0
  match twoBooleans.run initial with
  | .error error final => do
    check (expectResourceExhaustion error) "generated choice count cap should be resource exhaustion"
    check (final.cursor == 1 && final.generatedChoices == 1 && final.events.size == 1 && final.inputs.size == 1)
      "generated-choice exhaustion did not retain exactly the first successful choice"
    match final.inputs[0]?, final.events[0]? with
    | some (.boolean .floatEqual false), some event =>
      match event.request, event.input with
      | .boolean .floatEqual, .boolean .floatEqual false => pure ()
      | _, _ => throw (IO.userError "generated budget transcript mismatch")
    | _, _ => throw (IO.userError "generated budget did not retain exactly one transcript/input")
  | .ok _ _ => throw (IO.userError "two diagnostic calls exceeded a one-choice budget")

def zeroGeneratedChoiceBudget : IO Unit := do
  let initial := diagnosticTape 0 0
  match (ExecutionChoices.boolean tapeAccess .floatEqual).run initial with
  | .error error final => do
    check (expectResourceExhaustion error) "zero generated-choice budget should be resource exhaustion"
    check (final.cursor == 0 && final.generatedChoices == 0 && final.events.isEmpty && final.inputs.isEmpty)
      "zero generated-choice budget mutated tape"
  | .ok _ _ => throw (IO.userError "zero generated-choice budget unexpectedly generated input")

def policyConstructors : IO Unit := do
  let strict := strictTape #[.boolean .floatFuse false]
  check ((match strict.policy with | .strict => true | _ => false) && strict.cursor == 0 && strict.generatedChoices == 0 && strict.events.isEmpty)
    "strictTape constructor is not strict/default-empty"
  let diagnostic := diagnosticTape 7 9 #[.boolean .floatFuse false]
  check ((match diagnostic.policy with | .boundedDiagnostic 7 9 => true | _ => false) && diagnostic.inputs.size == 1 && diagnostic.cursor == 0)
    "diagnosticTape constructor did not retain exact explicit bounds/prefix"

#eval do
  strictExhaustion
  strictTranscript
  malformedStrictInput
  malformedDiagnosticInput
  emptyDomainsBeforeBudget
  bernoulliOutcomes
  invalidProbabilityBeforeDemand
  indexUsesExactCount
  integerLowerBoundary
  bytesBudgetAndExactLength
  diagnosticCursorGuard
  transcriptFreshness
  generatedChoiceBudget
  zeroGeneratedChoiceBudget
  policyConstructors
  IO.println "all diagnostic choice policy assertions passed"
