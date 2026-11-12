import Miri.Interpreter.HostStdioReplay
import Miri.Interpreter.Files
import Miri.Input.ExecutionChoicePolicy

open Miri.Interpreter
open HostStdio

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def isError (result : Except E A) : Bool :=
  match result with | .error _ => true | .ok _ => false

private def bytes : ByteArray := ⟨#[0, 255, 10]⟩
private def request : Request := .write .stderr bytes
private def row (response : Response) : Entry := ⟨request, response⟩

private structure State where
  replay : Option Replay := none
  choices : ExecutionChoices.Tape
  cleanupCount : Nat := 0

private def access : Access State := ⟨(·.replay), fun s r => {s with replay := r}⟩
private def choices : ExecutionChoices.Access State :=
  ⟨(·.choices), fun s tape => {s with choices := tape}⟩
private def initial : State := {
  replay := some {}
  choices := Miri.Input.ExecutionChoicePolicy.unboundedSeededDiagnosticTape 42
    #[.index .scheduler 1] }
private def action (entries : Array Entry) (r : Request := request) : EStateM StepError State Response :=
  perform access (some entries) r (throw (.unsupported "legacy stdio"))

-- This equality includes any legacy error and its partially mutated state.
private theorem disabled_exact (legacy : EStateM StepError State Response) :
    perform access none request legacy = legacy := perform_disabled ..

private def expectRejected (state : Replay) (r : Request := request) : IO Unit := do
  let (after, outcome) := consume r state
  match outcome with
  | .rejected _ =>
    check (after.cursor == state.cursor && after.fault.isSome && !complete after)
      "malformed row advanced cursor or became complete"
    let (again, _) := consume .flushStdout after
    check (again == after) "cleanup erased poisoned transcript"
  | _ => throw (IO.userError "malformed transcript was accepted")

def main : IO Unit := do
  let rawError : Error := ⟨.Interrupted, some 4⟩
  check (rawError.toHost.raw == some 4 && rawError.toHost.kind == .Interrupted)
    "host errno was dropped or inferred from ErrorKind"
  -- Short/zero writes, Interrupted and other errors are observations, not
  -- implicit success/retry. The source write_all loop owns retry semantics.
  for response in #[Response.write (.ok 0), .write (.ok 2), .write (.ok 3),
      .write (.error ⟨.Interrupted, some 4⟩), .write (.error ⟨.BrokenPipe, some 32⟩)] do
    let (after, result) := consume request {entries := #[row response]}
    check (result == .observed response && after.cursor == 1 && complete after)
      "valid exact host observation was changed"
  expectRejected {entries := #[row (.write (.ok 4))]}
  expectRejected {entries := #[row (.flush (.ok ()))]}
  expectRejected {entries := #[⟨.write .stdout bytes, .write (.ok 3)⟩]}
  expectRejected {entries := #[row (.write (.ok 3))]} (.write .stderr ⟨#[0, 254, 10]⟩)
  expectRejected {entries := #[row (.write (.ok 3))], cursor := 2}
  let flush : Entry := ⟨.flushStdout, .flush (.error ⟨.BrokenPipe, some 32⟩)⟩
  let (flushed, result) := consume .flushStdout {entries := #[flush]}
  check (result == .observed flush.response && complete flushed) "flush error was lost"
  check (!complete {entries := #[row (.write (.ok 3))]}) "unused suffix certified"
  check (gate (some {entries := #[row (.write (.ok 3))]}) ==
    .rejected "stdio transcript is not fully consumed") "zero-IO terminal consumed nonempty transcript"
  check (gate none == .rejected "stdio replay state is missing") "missing state certified"
  check (gate (some {pending := some ⟨1, request⟩}) ==
    .rejected "stdio pending ordinal is not the transcript tail") "forged ordinal authorized IO"
  let (_, wait) := consume request {}
  check (wait == .suspended ⟨0, request⟩) "first ordinal changed"
  let pending : Replay := {pending := some ⟨0, request⟩}
  check (appendResponse #[] pending (.write (.ok 2)) == .ok #[row (.write (.ok 2))])
    "tail response not appended exactly"
  check (isError (appendResponse #[] pending (.write (.ok 4)))) "oversize outer response accepted"
  check (isError (appendResponse #[] {pending with fault := some "cleanup mismatch"}
    (.write (.ok 2)))) "poisoned attempt authorized IO response"
  check (gateFor #[row (.write (.ok 3))] (some {}) ==
    .rejected "stdio attempt changed the committed transcript") "shortened zero-IO journal certified"
  check (gateFor #[row (.write (.ok 3))]
      (some {entries := #[row (.write (.ok 2))], cursor := 1}) ==
    .rejected "stdio attempt changed the committed transcript") "replaced complete journal certified"

  -- A failing destructor really replaces StepError in withDrop. The separate
  -- latch must survive, and its second request must not replace the first.
  let cleanup : EStateM StepError State Unit := do
    modify fun s => {s with cleanupCount := s.cleanupCount + 1}
    try
      let _ ← action #[] .flushStdout
    catch _ => pure ()
    throw (.invalidProgram "destructor failed after suspension")
  match (Files.withDrop (action #[]) cleanup).run initial with
  | .error (.invalidProgram _) after =>
    let some replay := after.replay | throw (IO.userError "cleanup lost replay state")
    check (replay.pending == some ⟨0, request⟩ && replay.cursor == 0 &&
      after.cleanupCount == 1 && !complete replay) "cleanup overwrote first request"
  | _ => throw (IO.userError "cleanup replacement control did not run")

  -- Both attempts begin from the identical supplied prefix/seed. Host replay
  -- neither consumes a semantic choice nor advances diagnostic RNG state.
  let choicePrefix : EStateM StepError State Nat := do
    let _ ← ExecutionChoices.index choices .scheduler 3
    ExecutionChoices.index choices .scheduler 7
  let .ok value before := choicePrefix.run initial | throw (IO.userError "choice prefix failed")
  let .error (.hostStdioRequest _) suspended := (action #[]).run before
    | throw (IO.userError "missing row did not suspend")
  check (reprStr suspended.choices == reprStr before.choices) "suspension mutated choices/RNG"
  let .ok same replayBefore := choicePrefix.run {initial with replay := some {entries := #[row (.write (.ok 3))]}}
    | throw (IO.userError "fresh prefix failed")
  check (same == value && reprStr replayBefore.choices == reprStr before.choices)
    "fresh seed/prefix did not reproduce diagnostic choices"
  let .ok _ after := (action #[row (.write (.ok 3))]).run replayBefore
    | throw (IO.userError "completed row failed on fresh attempt")
  check (reprStr after.choices == reprStr before.choices) "observation mutated choices/RNG"
  let .error (.invalidProgram _) poisoned :=
      (action #[row (.write (.ok 2))]).run after
    | throw (IO.userError "in-attempt transcript replacement accepted")
  check ((poisoned.replay.map (·.fault.isSome)).getD false) "changed transcript not poisoned"
  -- Exact same request twice with the slot lost between occurrences must not
  -- consume entry zero twice and certify two writes with one host observation.
  match (action #[row (.write (.ok 3))]).run {after with replay := none} with
  | .error (.invalidProgram _) lost =>
    check ((lost.replay.map (·.fault.isSome)).getD false) "lost cursor was reinitialized"
  | _ => throw (IO.userError "missing enabled state did not fail closed")
  IO.println "host stdio replay: passed (pure components; no host IO capability)"
