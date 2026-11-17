import duplicate_prefix.SuccessfulTrace
namespace DuplicatePrefix.SevenSteps
open Miri.Interpreter

theorem trace [DecidableEq K]
    {config : ExecutionMachine.Config K User Unit Other Extern Host} {limits : ExecutionMachine.Limits}
    {s0 s1 s2 s3 s4 s5 s6 s7 : MachineHooks.State K User}
    (e1 : ExecutionMachine.step config limits () s0 = (s1,.ok true))
    (e2 : ExecutionMachine.step config limits () s1 = (s2,.ok true))
    (e3 : ExecutionMachine.step config limits () s2 = (s3,.ok true))
    (e4 : ExecutionMachine.step config limits () s3 = (s4,.ok true))
    (e5 : ExecutionMachine.step config limits () s4 = (s5,.ok true))
    (e6 : ExecutionMachine.step config limits () s5 = (s6,.ok true))
    (e7 : ExecutionMachine.step config limits () s6 = (s7,.ok true)) :
    SuccessfulTrace.Trace config limits s0 s7 :=
  .next e1 (.next e2 (.next e3 (.next e4 (.next e5 (.next e6 (.next e7 (.refl _)))))))
#print axioms trace
end DuplicatePrefix.SevenSteps
