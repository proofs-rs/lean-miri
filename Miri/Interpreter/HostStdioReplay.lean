import Miri.Interpreter.IoError

/-! Pure checked replay of externally obtained standard-stream observations.
This module performs no IO. An outer runner must restart from the same initial
machine and exact choice policy/inputs after extending the immutable transcript.
Unwound suspension states are never resumable machine continuations. -/
namespace Miri.Interpreter.HostStdio

structure Error where
  kind : IoError.ErrorKind
  raw : Option Int32
  deriving Repr, DecidableEq

def Error.toHost (error : Error) : IoError.HostError Unit :=
  {kind := error.kind, raw := error.raw, payload := ()}

inductive Response where
  | write (result : Except Error Nat)
  | flush (result : Except Error Unit)
  deriving Repr, DecidableEq

structure Entry where
  request : Request
  response : Response
  deriving Repr, DecidableEq

structure Replay where
  entries : Array Entry := #[]
  cursor : Nat := 0
  /-- First wins, including when a destructor issues another request. -/
  pending : Option Pending := none
  /-- A mismatch poisons the attempt; later cleanup cannot make it valid. -/
  fault : Option String := none
  deriving Repr, DecidableEq

inductive Outcome where
  | observed (response : Response)
  | suspended (pending : Pending)
  | rejected (reason : String)
  deriving Repr, DecidableEq

def validResponse : Request → Response → Bool
  | .write _ bytes, .write (.ok count) => count <= bytes.size
  | .write .., .write (.error _) => true
  | .flushStdout, .flush _ => true
  | _, _ => false

/-- Never consumes a row on failure and never replaces an existing latch.
The request byte array is compared exactly, not by a lossy text encoding/hash. -/
def consume (request : Request) (state : Replay) : Replay × Outcome := Id.run do
  if let some reason := state.fault then return (state, .rejected reason)
  if let some pending := state.pending then return (state, .suspended pending)
  let reject := fun reason => ({state with fault := some reason}, .rejected reason)
  if state.cursor > state.entries.size then return reject "stdio cursor exceeds transcript"
  let some entry := state.entries[state.cursor]? | do
    let pending := {ordinal := state.cursor, request}
    return ({state with pending := some pending}, .suspended pending)
  if entry.request != request then return reject "stdio transcript request mismatch"
  unless validResponse request entry.response do return reject "stdio transcript response mismatch"
  return ({state with cursor := state.cursor + 1}, .observed entry.response)

/-- Every terminal outcome, including successful exit, needs this check before
certification. An unused suffix or retained pending/fault is not completion. -/
def complete (state : Replay) : Bool :=
  state.pending.isNone && state.fault.isNone && state.cursor == state.entries.size

inductive Gate where
  | complete
  | awaiting (pending : Pending)
  | rejected (reason : String)
  deriving Repr, DecidableEq

/-- The outer controller must apply this to every enabled attempt outcome
before rendering a terminal or considering a semantic-choice repair. -/
def gate : Option Replay → Gate
  | none => .rejected "stdio replay state is missing"
  | some state => Id.run do
    if let some reason := state.fault then return .rejected reason
    if let some pending := state.pending then
      if pending.ordinal != state.cursor || state.cursor != state.entries.size then
        return .rejected "stdio pending ordinal is not the transcript tail"
      return .awaiting pending
    if state.cursor != state.entries.size then return .rejected "stdio transcript is not fully consumed"
    return .complete

/-- Bind even zero-IO terminals to the outer committed journal. The controller
must use this gate, not only inspect the attempt state's self-reported rows. -/
def gateFor (entries : Array Entry) (state : Option Replay) : Gate :=
  match state with
  | none => gate none
  | some replay =>
    if replay.entries != entries then .rejected "stdio attempt changed the committed transcript"
    else gate state

/-- Produce only the next immutable input, not a resumable machine state.
Actual IO must happen only after `gate` authorizes its exact tail request. -/
def appendResponse (entries : Array Entry) (state : Replay) (response : Response) : Except String (Array Entry) := do
  match gateFor entries (some state) with
  | .awaiting pending =>
    unless validResponse pending.request response do throw "invalid host stdio response"
    return state.entries.push ⟨pending.request, response⟩
  | _ => throw "stdio attempt does not authorize a new response"

structure Access (S : Type) where
  get : S → Option Replay
  put : S → Option Replay → S

/-- `none` leaves the legacy callback literally unchanged. Enabling replay
requires an immutable transcript supplied by the outer attempt controller. -/
def perform (access : Access S) (entries : Option (Array Entry)) (request : Request)
    (legacy : EStateM StepError S Response) : EStateM StepError S Response :=
  match entries with
  | none => legacy
  | some entries => fun state =>
    -- Enabled attempts are installed exactly once on a fresh initial state.
    -- Missing state here can be a lost cursor/latch, never permission to reset.
    match access.get state with
    | none => .error (.invalidProgram "stdio replay state is missing")
        (access.put state (some {entries, fault := some "stdio replay state is missing"}))
    | some replay =>
      let replay := if replay.entries == entries then replay else
        {replay with fault := some "stdio transcript changed within an attempt"}
      let (replay, outcome) := consume request replay
      let state := access.put state (some replay)
      match outcome with
      | .observed response => .ok response state
      | .suspended pending => .error (.hostStdioRequest pending) state
      | .rejected reason => .error (.invalidProgram reason) state

theorem perform_disabled (access : Access S) (request : Request)
    (legacy : EStateM StepError S Response) :
    perform access none request legacy = legacy := rfl

theorem perform_missing (access : Access S) (entries : Array Entry) (request : Request)
    (legacy : EStateM StepError S Response) (state : S) (missing : access.get state = none) :
    perform access (some entries) request legacy state =
      .error (.invalidProgram "stdio replay state is missing")
        (access.put state (some {entries, fault := some "stdio replay state is missing"})) := by
  simp [perform, missing]

theorem consume_pending (request : Request) (state : Replay) (pending : Pending)
    (noFault : state.fault = none) (latched : state.pending = some pending) :
    consume request state = (state, .suspended pending) := by
  simp [consume, noFault, latched]

end Miri.Interpreter.HostStdio
