import Miri.Interpreter.ExecutionMachine
import Miri.Interpreter.ExecutionSafety

/-! Depth-scoped safety predicates over the production MIR machine. A trace
starts at a state whose stack depth is recorded in `IsCallEntry`. The boundary
tracks stack depth only: it does not establish that the same frame remains at
that depth (a tail call can replace a frame without changing depth). A caller's
continuation after a depth-decreasing pop is outside this claim. Resource
limits are fixed in `Context`, while the caller supplies the exact permitted
choice predicate. This is generic infrastructure: it does not yet establish
the predicates for duplicate_prefix.
-/

namespace DuplicatePrefix.CallSafety

open Miri.Interpreter

abbrev State (K User : Type) := MachineHooks.State K User

structure Context (K User Choice Other Extern Host : Type) [DecidableEq K] where
  machine : ExecutionMachine.Config K User Choice Other Extern Host
  limits : ExecutionMachine.Limits
  allowedChoice : State K User → Choice → Prop

def frameDepth (state : State K User) : Nat := state.stack.frames.size

/-- The current stack depth meets the entry threshold. This is deliberately a
depth test only; it does not identify a particular frame across tail calls.
-/
def inCall (entryDepth : Nat) (state : State K User) : Prop :=
  entryDepth ≤ frameDepth state

def pastCallBoundary (entryDepth : Nat) (state : State K User) : Prop :=
  frameDepth state < entryDepth

/-- The scoped claim starts from an installed, nonempty target frame. -/
def IsCallEntry (entryDepth : Nat) (initial : State K User) : Prop :=
  0 < entryDepth ∧ frameDepth initial = entryDepth

/-- A single actual `ExecutionMachine.step` whose source lies inside the call.
The machine configuration and resource limits are fixed by `Context`.
-/
def ScopedStep [DecidableEq K] (context : Context K User Choice Other Extern Host)
    (entryDepth : Nat) (before after : State K User)
    (outcome : Except StepError Bool) : Prop :=
  inCall entryDepth before ∧
    ∃ choice, context.allowedChoice before choice ∧
      ExecutionMachine.step context.machine context.limits choice before = (after, outcome)

/-- States reachable by successful continuing steps before crossing the depth
boundary. A pop may reach a state below `entryDepth`, but no later step is
added from that state. Equal-depth frame replacement is still inside this
depth-scoped relation.
-/
inductive Reachable [DecidableEq K]
    (context : Context K User Choice Other Extern Host)
    (entryDepth : Nat) (initial : State K User) : State K User → Prop where
  | initial : Reachable context entryDepth initial initial
  | next {before after : State K User}
      (reachablePrefix : Reachable context entryDepth initial before)
      (step : ScopedStep context entryDepth before after (.ok true)) :
      Reachable context entryDepth initial after

def isUndefinedBehavior : Except StepError Bool → Prop
  | .error error => RunLoop.reportsUB error = true
  | _ => False

/-- No interpreter-classified UB error is possible at any reachable state
whose depth meets the entry threshold, for any choice admitted by the explicit
predicate. The boundary itself does not distinguish return from unwind.
-/
def NoUBBeforeReturn [DecidableEq K]
    (context : Context K User Choice Other Extern Host)
    (entryDepth : Nat) (initial : State K User) : Prop :=
  IsCallEntry entryDepth initial ∧
  ∀ state, Reachable context entryDepth initial state → inCall entryDepth state →
    ∀ choice, context.allowedChoice state choice →
      ∀ after outcome,
        ExecutionMachine.step context.machine context.limits choice state = (after, outcome) →
        ¬ isUndefinedBehavior outcome

/-- Stronger depth-scoped property: no interpreter error of any kind can occur
while the reachable stack depth meets the entry threshold. Unsupported
outcomes, retag-write failures and non-UB termination errors are included.
-/
def NoErrorsBeforeReturn [DecidableEq K]
    (context : Context K User Choice Other Extern Host)
    (entryDepth : Nat) (initial : State K User) : Prop :=
  IsCallEntry entryDepth initial ∧
  ∀ state, Reachable context entryDepth initial state → inCall entryDepth state →
    ∀ choice, context.allowedChoice state choice →
      ∀ after outcome,
        ExecutionMachine.step context.machine context.limits choice state = (after, outcome) →
        ∃ value, outcome = .ok value

theorem noErrors_implies_noUB [DecidableEq K]
    (context : Context K User Choice Other Extern Host)
    (entryDepth : Nat) (initial : State K User)
    (safe : NoErrorsBeforeReturn context entryDepth initial) :
    NoUBBeforeReturn context entryDepth initial := by
  constructor
  · exact safe.1
  · intro state reachable active choice permitted after outcome step
    obtain ⟨value, hvalue⟩ := safe.2 state reachable active choice permitted after outcome step
    simp [isUndefinedBehavior, hvalue]

/-- Invariants can be lifted along the actual depth-scoped step relation. A
depth-decreasing pop may make the invariant irrelevant to later caller steps.
-/
theorem invariant_on_reachable [DecidableEq K]
    (context : Context K User Choice Other Extern Host)
    (entryDepth : Nat) (initial : State K User) (invariant : State K User → Prop)
    (initialInvariant : invariant initial)
    (preserved : ∀ {before after}, Reachable context entryDepth initial before →
      inCall entryDepth before →
      (∃ choice, context.allowedChoice before choice ∧
        ExecutionMachine.step context.machine context.limits choice before = (after, .ok true)) →
      invariant before → invariant after) :
    ∀ state, Reachable context entryDepth initial state → invariant state := by
  intro state reachable
  induction reachable with
  | initial => exact initialInvariant
  | @next before after reachablePrefix step ih =>
    rcases step with ⟨active, choice, permitted, stepEq⟩
    exact preserved reachablePrefix active ⟨choice, permitted, stepEq⟩ ih

/-- A depth-decreasing frame pop is only a scope boundary here; this does not
classify the pop as normal return rather than unwind. `ScopedStep` cannot start
below the recorded depth. A tail-call replacement at the same depth remains
inside the relation because frame identity is not tracked.
-/
theorem no_scoped_step_after_return [DecidableEq K]
    (context : Context K User Choice Other Extern Host)
    (entryDepth : Nat) (state : State K User)
    (returned : pastCallBoundary entryDepth state) :
    ¬ ∃ after outcome, ScopedStep context entryDepth state after outcome := by
  rintro ⟨after, outcome, active, _⟩
  exact (Nat.not_le_of_gt returned) active

/-- Apply a state invariant to discharge the stronger local outcome check on
every reachable in-call state. `preserved` must be proved from the actual
execution machine for the selected client; this theorem supplies no semantics
or client invariant.
-/
theorem noErrors_of_invariant [DecidableEq K]
    (context : Context K User Choice Other Extern Host)
    (entryDepth : Nat) (initial : State K User) (invariant : State K User → Prop)
    (callEntry : IsCallEntry entryDepth initial)
    (initialInvariant : invariant initial)
    (preserved : ∀ {before after}, Reachable context entryDepth initial before →
      inCall entryDepth before →
      (∃ choice, context.allowedChoice before choice ∧
        ExecutionMachine.step context.machine context.limits choice before = (after, .ok true)) →
      invariant before → invariant after)
    (localSafety : ∀ state, Reachable context entryDepth initial state →
      inCall entryDepth state → invariant state →
      ∀ choice, context.allowedChoice state choice →
      ∀ after outcome,
        ExecutionMachine.step context.machine context.limits choice state = (after, outcome) →
        ∃ value, outcome = .ok value) :
    NoErrorsBeforeReturn context entryDepth initial := by
  constructor
  · exact callEntry
  · intro state reachable active choice permitted after outcome step
    exact localSafety state reachable active
      (invariant_on_reachable context entryDepth initial invariant initialInvariant preserved state reachable)
      choice permitted after outcome step

#print axioms noErrors_implies_noUB
#print axioms invariant_on_reachable
#print axioms no_scoped_step_after_return
#print axioms noErrors_of_invariant

end DuplicatePrefix.CallSafety
