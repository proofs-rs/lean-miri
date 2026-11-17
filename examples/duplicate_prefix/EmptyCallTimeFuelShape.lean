import duplicate_prefix.DuplicatePrefixCallSpecification
namespace DuplicatePrefix.EmptyCallTimeFuelShape
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
open DuplicatePrefixCallSpecification
set_option autoImplicit false
/-- The concrete initial-data budget supplies the successor-shaped counters
used by existing empty-call adapters. This is not a proof that the budget is
sufficient for every interpreter operation. No execution result is assumed. -/
theorem derive {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {before : Before} {tracker : MachineHooks.BorrowState} {len : UInt64}
    (resources : Resources options limits remaining before tracker len) :
    ∃ dynamicFuel validityFuel budget,
      options.place.dynamicFuel = dynamicFuel+1 ∧
      options.limits.validation = validityFuel+1 ∧ limits.callDispatch = budget+1 := by
  have floor : 64 ≤ work before len := by unfold work; omega
  have dynamic := resources.dynamicFuel
  have validity := resources.configuredFuel
  have dispatch := resources.executionFuel
  simp only [fuelAtLeast] at validity dispatch
  refine ⟨options.place.dynamicFuel-1,options.limits.validation-1,limits.callDispatch-1,?_,?_,?_⟩ <;> omega
end DuplicatePrefix.EmptyCallTimeFuelShape
