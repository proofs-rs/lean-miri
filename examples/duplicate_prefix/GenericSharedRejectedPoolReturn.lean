import duplicate_prefix.GenericSharedRejectedReturn
import duplicate_prefix.GenericSharedRejectedPoolRuntime
namespace DuplicatePrefix.GenericSharedRejectedPoolReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
theorem complete (s : GenericSharedRejectedPoolInput.Input) :
    let config := PreparedContracts.actualConfig s.options () (s.remaining+1) s.span
    let initial := Storage.withCurrent #[] s.frame s.machine
    ∃ ready : GenericRootRejectedPhysical.Input, ∃ finalState,
      GenericRootRejectedPhysical.Result ready ∧
      SuccessfulTrace.Trace config s.limits initial finalState ∧
      ExecutionMachine.step config s.limits () finalState = (finalState,.ok false) ∧
      finalState.stack.frames = #[] ∧
      CallSafety.NoUBBeforeReturn
        (⟨config,s.limits,fun _ _ => True⟩ : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit)
        1 initial ∧
      (∀ before, SuccessfulTrace.Trace config s.limits initial before →
        ∃ after continuing, ExecutionMachine.step config s.limits () before = (after,.ok continuing)) :=
  GenericSharedRejectedReturn.complete_with_prefix s (GenericSharedRejectedPoolRuntime.prepare s)
end DuplicatePrefix.GenericSharedRejectedPoolReturn
