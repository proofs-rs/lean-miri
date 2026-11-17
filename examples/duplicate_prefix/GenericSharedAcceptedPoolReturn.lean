import duplicate_prefix.GenericSharedAcceptedPoolRuntime
import duplicate_prefix.GenericAsMutDefaultPoolReturn
namespace DuplicatePrefix.GenericSharedAcceptedPoolReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

/-- One initial accepted-branch state at PC2:11 executes both shared reborrows,
len/release, the mutable expression and as_mut_ptr, then the actual copy and
physical true return. All intermediate data and operational success are derived. -/
theorem complete (s : GenericSharedAcceptedInput.PoolInput) :
    let config := PreparedContracts.actualConfig s.options () (s.remaining+1) s.span
    let initial := Storage.withCurrent #[] s.frame s.machine
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
  let config := PreparedContracts.actualConfig s.options () (s.remaining+1) s.span
  let initial := Storage.withCurrent #[] s.frame s.machine
  obtain ⟨suffix,configEq,limitsEq,leadingTrace⟩ := GenericSharedAcceptedPoolRuntime.prepare s
  obtain ⟨ready,finalState,physical,tail,terminal,empty,_,_⟩ := GenericAsMutDefaultPoolReturn.complete suffix
  rw [configEq,limitsEq] at tail terminal
  have full : SuccessfulTrace.Trace config s.limits initial finalState := SuccessfulTrace.append leadingTrace tail
  have safety := SuccessfulTrace.no_ub
    (⟨config,s.limits,fun _ _ => True⟩ : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit)
    1 initial finalState ⟨by decide,rfl⟩ full (by rw [CallSafety.pastCallBoundary,CallSafety.frameDepth,empty];change 0 < 1;decide)
  exact ⟨ready,finalState,physical,full,terminal,empty,safety,
    SuccessfulTraceTerminal.prefix_step_success full terminal⟩
end DuplicatePrefix.GenericSharedAcceptedPoolReturn
