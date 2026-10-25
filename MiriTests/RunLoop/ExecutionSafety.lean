import Miri.Interpreter.ExecutionSafety

open Miri.Interpreter Miri.Interpreter.RunLoop

namespace ExecutionSafetyTests

/-- An explicit tiny machine fixture: false continues forever, true reports UB.
This tests the scheduler-prefix definitions, not any Rust language rule. -/
def hooks : RunLoopHooks Nat Bool Unit where
  coreStep choice state := if choice then (state, .error (.undefinedBehavior "fixture"))
    else (state + 1, .ok true)
  takeStackEmptyCallback state := (state, .error (.unsupported "fixture callback"))
  invokeStackEmptyCallback _ _ state := (state, .error (.unsupported "fixture callback"))
  restoreStackEmptyCallback _ state := (state, .ok ())
  terminateActiveThread _ _ state := (state, .error (.unsupported "fixture termination"))
  interrupted _ := false
  handleAbnormalTermination state := state
  schedule _ state := (state, .ok .executeStep)
  communicate _ := false
  pollAndUnblock _ _ state := (state, .error (.unsupported "fixture IO"))
  sleep _ _ state := (state, .error (.unsupported "fixture clock"))

/-- All finite prefixes of a nonterminating machine can be UB free. -/
example : UBFreedomFrom hooks (fun _ choice => choice = false) (fun state => state = 0) := by
  apply ubFreedomFrom_of_invariant hooks (fun _ choice => choice = false)
    (fun state => state = 0) (fun _ => True)
  · intros; trivial
  · intros; trivial
  · intro before after choice error _ hchoice hstep
    subst choice
    simp [iteration, stepCurrentThread, hooks] at hstep

/-- The identical machine is unsafe when its other choice is permitted. -/
theorem unsafe_all_choices : UBReachable hooks (fun _ _ => True) (fun state => state = 0) := by
  refine ⟨.undefinedBehavior "fixture", ?_, rfl⟩
  refine ⟨0, 0, true, ?_, trivial, rfl⟩
  exact ⟨0, [], rfl, .nil 0⟩

example : ¬ UBFreedomFrom hooks (fun _ _ => True) (fun state => state = 0) :=
  not_ubFreedomFrom_of_ubReachable hooks _ _ unsafe_all_choices

/-- A finite witness may include successful iterations before the error. -/
example : ReachesError hooks (fun _ _ => True) (fun state => state = 0)
    (.undefinedBehavior "fixture") := by
  refine ⟨2, 2, true, ?_, trivial, rfl⟩
  refine ⟨0, [false, false], rfl, ?_⟩
  exact .cons trivial rfl (.cons trivial rfl (.nil 2))

/-- Absence of a UB label is not evidence that a missing operation is safe. -/
example : reportsUB (.unsupported "missing operation") = false := rfl
example : reportsUB (.resourceExhaustion "budget") = false := rfl

end ExecutionSafetyTests
