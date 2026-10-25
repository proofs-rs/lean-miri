import Miri.Interpreter.ExecutionSafety
import Miri.OperationalSafety
open Miri.Interpreter
namespace SafetyReview

def halted (error : StepError) : RunLoopHooks Unit Unit Unit where
  coreStep := fun _ s => (s, .ok true)
  takeStackEmptyCallback := fun s => (s, .ok ())
  invokeStackEmptyCallback := fun _ _ s => (s, .ok .pending)
  restoreStackEmptyCallback := fun _ s => (s, .ok ())
  terminateActiveThread := fun _ _ s => (s, .ok ())
  interrupted := fun _ => false
  handleAbnormalTermination := id
  schedule := fun _ s => (s, .error error)
  communicate := fun _ => false
  pollAndUnblock := fun _ _ s => (s, .ok ())
  sleep := fun _ _ s => (s, .ok ())

theorem conditionalOnly (error : StepError) (notUB : RunLoop.reportsUB error = false) :
    RunLoop.UBFreedomFrom (halted error) (fun _ _ => True) (fun _ => True) := by
  apply RunLoop.ubFreedomFrom_of_invariant _ _ _ (fun _ => True)
  · intro _ _; trivial
  · intro _ _ _ _ _ _; trivial
  · intro before after choice observed _ _ result
    simp [RunLoop.iteration, halted] at result
    cases result
    exact notUB

example : RunLoop.UBFreedomFrom (halted (.unsupported "absent operation"))
    (fun _ _ => True) (fun _ => True) := conditionalOnly _ rfl
example : RunLoop.UBFreedomFrom (halted (.resourceExhaustion "construction capacity"))
    (fun _ _ => True) (fun _ => True) := conditionalOnly _ rfl
#print axioms conditionalOnly
end SafetyReview
