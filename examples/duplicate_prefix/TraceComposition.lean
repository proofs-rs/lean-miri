import duplicate_prefix.SuccessfulTrace
namespace DuplicatePrefix.TraceComposition
open Miri.Interpreter

theorem ten [DecidableEq K]
    {config : ExecutionMachine.Config K User Unit Other Extern Host} {limits : ExecutionMachine.Limits}
    {s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 : MachineHooks.State K User}
    (e1 : ExecutionMachine.step config limits () s0 = (s1,.ok true))
    (e2 : ExecutionMachine.step config limits () s1 = (s2,.ok true))
    (e3 : ExecutionMachine.step config limits () s2 = (s3,.ok true))
    (e4 : ExecutionMachine.step config limits () s3 = (s4,.ok true))
    (e5 : ExecutionMachine.step config limits () s4 = (s5,.ok true))
    (e6 : ExecutionMachine.step config limits () s5 = (s6,.ok true))
    (e7 : ExecutionMachine.step config limits () s6 = (s7,.ok true))
    (e8 : ExecutionMachine.step config limits () s7 = (s8,.ok true))
    (e9 : ExecutionMachine.step config limits () s8 = (s9,.ok true))
    (e10 : ExecutionMachine.step config limits () s9 = (s10,.ok true)) :
    SuccessfulTrace.Trace config limits s0 s10 :=
  .next e1 (.next e2 (.next e3 (.next e4 (.next e5 (.next e6 (.next e7 (.next e8 (.next e9 (.next e10 (.refl _))))))))))

#print axioms ten
end DuplicatePrefix.TraceComposition
