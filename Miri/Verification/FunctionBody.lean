import Miri.Interpreter.RunLoop

/-! Safety from a prepared callee frame through the step that returns to its
caller. A successful step below the entry depth ends the scope. -/
namespace Miri.Verification.FunctionBody

open Miri.Interpreter

variable {S C : Type}

/-- Finite successful prefixes in the scope; the final state may be the caller. -/
inductive Reachable (step : C → S → StepResult S Bool) (stackDepth : S → Nat)
    (allowed : S → C → Prop) (depth : Nat) (start : S) : S → Prop where
  | initial : Reachable step stackDepth allowed depth start start
  | next {before after : S} {choice : C} :
      Reachable step stackDepth allowed depth start before →
      depth ≤ stackDepth before → allowed before choice →
      step choice before = (after, .ok true) →
      Reachable step stackDepth allowed depth start after

/-- Error postcondition for every observed error while the callee is in scope. -/
def OnError (step : C → S → StepResult S Bool) (stackDepth : S → Nat)
    (allowed : S → C → Prop) (depth : Nat) (start : S) (post : StepError → S → Prop) : Prop :=
  ∀ before, Reachable step stackDepth allowed depth start before →
    depth ≤ stackDepth before → ∀ choice, allowed before choice →
      ∀ after error, step choice before = (after, .error error) → post error after

/-- Every observed error while the callee is in scope is classified non-UB. -/
def UBFree (step : C → S → StepResult S Bool) (stackDepth : S → Nat)
    (allowed : S → C → Prop) (depth : Nat) (start : S) : Prop :=
  OnError step stackDepth allowed depth start (fun error _ => RunLoop.reportsUB error = false)

/-- A predicate on states reached below the prepared frame's entry depth.
A postcondition can require the caller's normal continuation. -/
def NormalPost (step : C → S → StepResult S Bool) (stackDepth : S → Nat)
    (allowed : S → C → Prop) (depth : Nat) (start : S) (post : S → Prop) : Prop :=
  ∀ after, Reachable step stackDepth allowed depth start after → stackDepth after < depth → post after

theorem ofInvariant {step : C → S → StepResult S Bool} {stackDepth allowed depth start post}
    (invariant : S → Prop) (initial : invariant start)
    (preserved : ∀ before after choice, invariant before → depth ≤ stackDepth before →
      allowed before choice → step choice before = (after, .ok true) → invariant after)
    (safe : ∀ before after choice error, invariant before → depth ≤ stackDepth before →
      allowed before choice → step choice before = (after, .error error) → RunLoop.reportsUB error = false)
    (onReturn : ∀ after, invariant after → stackDepth after < depth → post after) :
    UBFree step stackDepth allowed depth start ∧ NormalPost step stackDepth allowed depth start post := by
  have inv : ∀ after, Reachable step stackDepth allowed depth start after → invariant after := by
    intro after reachable
    induction reachable with
    | initial => exact initial
    | next _ inside permitted outcome ih => exact preserved _ _ _ ih inside permitted outcome
  exact ⟨fun before reach inside choice permitted after error outcome =>
    safe before after choice error (inv before reach) inside permitted outcome,
    fun after reach outside => onReturn after (inv after reach) outside⟩

/-- Check the actual preparation error or the body entered by preparation. -/
def CallNoUB (step : C → S → StepResult S Bool) (stackDepth : S → Nat)
    (allowed : S → C → Prop) (depth : Nat) (prepare : EStateM.Result StepError S Unit) : Prop :=
  match prepare with
  | .error error _ => RunLoop.reportsUB error = false
  | .ok () entry => depth ≤ stackDepth entry ∧ UBFree step stackDepth allowed depth entry

/-- Compose the error condition on actual preparation with the callee body proof. -/
theorem CallNoUB.of_preparation {step : C → S → StepResult S Bool} {stackDepth allowed depth}
    (prepare : EStateM.Result StepError S Unit) (pre : S → Prop)
    (prepareError : ∀ failed error, prepare = .error error failed → RunLoop.reportsUB error = false)
    (prepared : ∀ entry, prepare = .ok () entry → depth ≤ stackDepth entry ∧ pre entry)
    (body : ∀ entry, pre entry → UBFree step stackDepth allowed depth entry) :
    CallNoUB step stackDepth allowed depth prepare := by
  cases outcome : prepare with
  | error error state => exact prepareError state error outcome
  | ok value state =>
    cases value
    have ready := prepared state outcome
    exact ⟨ready.1, body state ready.2⟩

end Miri.Verification.FunctionBody
