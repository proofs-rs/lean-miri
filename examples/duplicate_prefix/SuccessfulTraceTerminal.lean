import duplicate_prefix.SuccessfulTrace

namespace DuplicatePrefix.SuccessfulTraceTerminal
open Miri.Interpreter
set_option maxHeartbeats 200000

/-- A deterministic Unit-choice trace ending at a normal terminal state rules
out every interpreter error after every actual successful finite prefix. The
claim includes depth-decreasing steps and requires no call-entry depth match. -/
theorem prefix_step_success [DecidableEq K]
    {config : ExecutionMachine.Config K User Unit Other Extern Host} {limits : ExecutionMachine.Limits}
    {initial done : MachineHooks.State K User}
    (trace : SuccessfulTrace.Trace config limits initial done)
    (terminal : ExecutionMachine.step config limits () done = (done,.ok false)) :
    ∀ before, SuccessfulTrace.Trace config limits initial before →
      ∃ after continuing, ExecutionMachine.step config limits () before = (after,.ok continuing) := by
  induction trace with
  | refl =>
    intro before execution
    cases execution with
    | refl => exact ⟨_,false,terminal⟩
    | next step tail =>
      rw [terminal] at step
      cases step
  | next step tail ih =>
    intro before execution
    cases execution with
    | refl => exact ⟨_,true,step⟩
    | next nextStep later =>
      have equal := congrArg Prod.fst (step.symm.trans nextStep)
      dsimp only at equal
      cases equal
      exact ih terminal before later

end DuplicatePrefix.SuccessfulTraceTerminal
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.SuccessfulTraceTerminal.prefix_step_success) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved finite-prefix terminal-trace dependency {dependency}"
