import duplicate_prefix.GenericSharedRejectedRuntime
import duplicate_prefix.SuccessfulTraceTerminal
namespace DuplicatePrefix.GenericSharedRejectedReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

/-- Complete the positive-count rejected branch from initial PC2:11 data,
including both shared reborrows, actual len/helper return, the rejected guard,
root release and physical byte-zero return. No intermediate Data or successful
operation is assumed. -/
theorem complete_with_prefix (s : GenericSharedRejectedInput.Base)
    (prepared : ∃ ready : GenericRootRejectedPhysical.Input,
      PreparedContracts.actualConfig ready.options () (ready.remaining+1) ready.span =
        PreparedContracts.actualConfig s.options () (s.remaining+1) s.span ∧ ready.limits=s.limits ∧
      SuccessfulTrace.Trace (PreparedContracts.actualConfig s.options () (s.remaining+1) s.span) s.limits
        (Storage.withCurrent #[] s.frame s.machine) (Storage.withCurrent #[] ready.before ready.machine)) :
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
        ∃ after continuing, ExecutionMachine.step config s.limits () before = (after,.ok continuing)) := by
  obtain ⟨ready,configEq,limitsEq,prefixTrace⟩ := prepared
  have physical := GenericRootRejectedPhysical.complete ready
  obtain ⟨updated,tail,terminal,_,_⟩ := physical
  let finalState := CanonicalCopy.replaceAllocation (GenericRootRejectedPhysical.popped ready) ready.release.slotId ready.release.slot.kind updated
  rw [configEq,limitsEq] at tail terminal
  have full := SuccessfulTrace.append prefixTrace tail
  have empty : finalState.stack.frames = #[] := rfl
  have safety := SuccessfulTrace.no_ub
    (⟨PreparedContracts.actualConfig s.options () (s.remaining+1) s.span,s.limits,fun _ _ => True⟩ :
      CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit)
    1 (Storage.withCurrent #[] s.frame s.machine) finalState ⟨by decide,rfl⟩ full
    (by rw [CallSafety.pastCallBoundary,CallSafety.frameDepth,empty];change 0 < 1;decide)
  exact ⟨ready,finalState,GenericRootRejectedPhysical.complete ready,full,terminal,empty,safety,SuccessfulTraceTerminal.prefix_step_success full terminal⟩

theorem complete (s : GenericSharedRejectedInput.Input) :
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
  complete_with_prefix s (GenericSharedRejectedRuntime.prepare s)
end DuplicatePrefix.GenericSharedRejectedReturn
