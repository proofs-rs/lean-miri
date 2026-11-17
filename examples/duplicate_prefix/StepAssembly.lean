import Miri.Interpreter.ExecutionMachine

namespace DuplicatePrefix.StepAssembly
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

set_option maxRecDepth 8192

theorem with_validation_twice [DecidableEq K]
    (config : ExecutionMachine.Config K User Choice Other Extern Host)
    (limits : ExecutionMachine.Limits) :
    ExecutionMachine.withValidation (ExecutionMachine.withValidation config limits) limits =
      ExecutionMachine.withValidation config limits := by rfl

theorem rvalue_hooks_validated [DecidableEq K]
    (config : ExecutionMachine.Config K User Choice Other Extern Host)
    (limits : ExecutionMachine.Limits) :
    ExecutionMachine.rvalueHooks (ExecutionMachine.withValidation config limits) limits =
      ExecutionMachine.rvalueHooks config limits := by
  unfold ExecutionMachine.rvalueHooks
  rw [with_validation_twice]

theorem assign [DecidableEq K]
    (config : ExecutionMachine.Config K User Choice Other Extern Host)
    (limits : ExecutionMachine.Limits) (choice : Choice) (place : Place) (value : Rvalue) :
    (ExecutionMachine.stepHooks config limits).assign choice place value =
      MachineHooks.run (evalRvalueIntoPlace (ExecutionMachine.rvalueHooks config limits) choice value place) := by
  change MachineHooks.run (evalRvalueIntoPlace
    (ExecutionMachine.rvalueHooks (ExecutionMachine.withValidation config limits) limits)
      choice value place) = _
  rw [rvalue_hooks_validated]

#print axioms assign
end DuplicatePrefix.StepAssembly
