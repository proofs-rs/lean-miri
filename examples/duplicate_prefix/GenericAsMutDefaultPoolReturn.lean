import duplicate_prefix.GenericAsMutDefaultReturn
import duplicate_prefix.GenericAsMutDefaultPoolToCall

namespace DuplicatePrefix.GenericAsMutDefaultPoolReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

/-- Execute the actual mutable expression, as_mut_ptr, copy and physical terminal
return from original PC6:7 ownership/runtime/storage and arbitrary coherent-pool
data. Subsequent call Data and operation success are derived internally. -/
theorem complete (input : GenericAsMutDefaultPoolToCall.Input) :
    let s := input.common.base.data.start
    let config := PreparedContracts.actualConfig s.options () (s.remaining+1) s.span
    let initial := Storage.withCurrent #[] input.common.base.caller s.machine
    ∃ ready : GenericAsMutPhysicalReturn.Input, ∃ finalState,
      GenericAsMutPhysicalReturn.Result ready ∧
      SuccessfulTrace.Trace config s.limits initial finalState ∧
      ExecutionMachine.step config s.limits () finalState = (finalState,.ok false) ∧
      finalState.stack.frames = #[] ∧
      CallSafety.NoUBBeforeReturn
        (⟨config,s.limits,fun _ _ => True⟩ : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit)
        1 initial ∧
      (∀ before, SuccessfulTrace.Trace config s.limits initial before →
        ∃ after continuing, ExecutionMachine.step config s.limits () before = (after,.ok continuing)) := by
  obtain ⟨call,frameEq,machineEq,configEq,limitsEq⟩ := GenericAsMutDefaultPoolToCall.prepare input
  exact GenericAsMutDefaultReturn.complete_of_prepared input.common.base call frameEq machineEq configEq limitsEq
end DuplicatePrefix.GenericAsMutDefaultPoolReturn
