import duplicate_prefix.GeneralBorrowForestAsMutDefaultToCall
namespace DuplicatePrefix.GeneralBorrowForestAsMutDefaultReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

/-- From the actual root PC6:7 state, execute mutable expression, as_mut_ptr,
copy and physical true return. The initial contract contains graph, storage,
slot and fixed-runtime data only. -/
theorem complete_of_prepared (base : GeneralBorrowForestAsMutDefaultCore.Input)
    (call : GeneralBorrowForestAsMutCallToReturn.Input)
    (frameEq : call.caller = GeneralBorrowForestAsMutDefaultCore.frame base)
    (machineEq : call.data.start.machine = GeneralBorrowForestAsMutDefaultCore.machine base.data.start)
    (configEq : PreparedContracts.actualConfig call.data.start.options () (call.data.start.remaining+1) call.data.start.span =
      PreparedContracts.actualConfig base.data.start.options () (base.data.start.remaining+1) base.data.start.span)
    (limitsEq : call.data.start.limits = base.data.start.limits) :
    let s := base.data.start
    let config := PreparedContracts.actualConfig s.options () (s.remaining+1) s.span
    let initial := Storage.withCurrent #[] base.caller s.machine
    ∃ ready : GeneralBorrowForestAsMutPhysicalReturn.Input, ∃ finalState,
      GeneralBorrowForestAsMutPhysicalReturn.Result ready ∧
      SuccessfulTrace.Trace config s.limits initial finalState ∧
      ExecutionMachine.step config s.limits () finalState = (finalState,.ok false) ∧
      finalState.stack.frames = #[] ∧
      CallSafety.NoUBBeforeReturn
        (⟨config,s.limits,fun _ _ => True⟩ : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit)
        1 initial ∧
      (∀ before, SuccessfulTrace.Trace config s.limits initial before →
        ∃ after continuing, ExecutionMachine.step config s.limits () before = (after,.ok continuing)) := by
  let s := base.data.start
  let config := PreparedContracts.actualConfig s.options () (s.remaining+1) s.span
  let initial := Storage.withCurrent #[] base.caller s.machine
  obtain ⟨ready,finalState,physical,tail,terminal,empty,_,_⟩ := GeneralBorrowForestAsMutCallToReturn.complete call
  rw [configEq,limitsEq,frameEq,machineEq] at tail
  rw [configEq,limitsEq] at terminal
  have full : SuccessfulTrace.Trace config s.limits initial finalState :=
    .next (GeneralBorrowForestAsMutDefaultCore.step base) tail
  have safety := SuccessfulTrace.no_ub
    (⟨config,s.limits,fun _ _ => True⟩ : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit)
    1 initial finalState ⟨by decide,rfl⟩ full (by rw [CallSafety.pastCallBoundary,CallSafety.frameDepth,empty];change 0 < 1;decide)
  exact ⟨ready,finalState,physical,full,terminal,empty,safety,
    SuccessfulTraceTerminal.prefix_step_success full terminal⟩
theorem complete (input : GeneralBorrowForestAsMutDefaultToCall.Input) :
    let s := input.base.data.start
    let config := PreparedContracts.actualConfig s.options () (s.remaining+1) s.span
    let initial := Storage.withCurrent #[] input.base.caller s.machine
    ∃ ready : GeneralBorrowForestAsMutPhysicalReturn.Input, ∃ finalState,
      GeneralBorrowForestAsMutPhysicalReturn.Result ready ∧
      SuccessfulTrace.Trace config s.limits initial finalState ∧
      ExecutionMachine.step config s.limits () finalState = (finalState,.ok false) ∧
      finalState.stack.frames = #[] ∧
      CallSafety.NoUBBeforeReturn
        (⟨config,s.limits,fun _ _ => True⟩ : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit)
        1 initial ∧
      (∀ before, SuccessfulTrace.Trace config s.limits initial before →
        ∃ after continuing, ExecutionMachine.step config s.limits () before = (after,.ok continuing)) := by
  obtain ⟨call,frameEq,machineEq,configEq,limitsEq⟩ := GeneralBorrowForestAsMutDefaultToCall.prepare input
  exact complete_of_prepared input.base call frameEq machineEq configEq limitsEq

end DuplicatePrefix.GeneralBorrowForestAsMutDefaultReturn
