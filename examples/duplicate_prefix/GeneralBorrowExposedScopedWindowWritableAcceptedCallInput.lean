import duplicate_prefix.GeneralBorrowExposedScopedWindowWritableAcceptedAfterLen
import duplicate_prefix.GeneralBorrowExposedScopedWindowWritableAcceptedToAsMut
namespace DuplicatePrefix.GeneralBorrowExposedScopedWindowWritableAcceptedCallInput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

theorem prepare (s : GeneralBorrowExposedScopedWindowWritableAcceptedAfterLen.Initial) :
    ∃ (expression : GeneralBorrowExposedScopedWindowWritableAcceptedExpression.Input) (call : GeneralBorrowExposedScopedWindowWritableAsMutCallInput.Input),
      GeneralBorrowExposedScopedWindowWritableAcceptedAfterLen.Origin s expression ∧
      GeneralBorrowExposedScopedWindowWritableAcceptedToAsMut.Origin expression call ∧
      SuccessfulTrace.Trace (ActualReferenceContext.config s.options (s.remaining+1) s.span) s.limits
        (Storage.withCurrent #[] s.caller s.machine) (Storage.withCurrent #[] call.caller call.machine) := by
  obtain ⟨expression,origin,prefixTrace⟩:=GeneralBorrowExposedScopedWindowWritableAcceptedAfterLen.prepare s
  obtain ⟨call,callOrigin,step⟩:=GeneralBorrowExposedScopedWindowWritableAcceptedToAsMut.forms expression
  have step' : ExecutionMachine.step (ActualReferenceContext.config s.options (s.remaining+1) s.span) s.limits ()
      (Storage.withCurrent #[] expression.caller expression.machine)=(Storage.withCurrent #[] call.caller call.machine,.ok true) := by
    simpa only [origin.options,origin.remaining,origin.span,origin.limits] using step
  exact ⟨expression,call,origin,callOrigin,SuccessfulTrace.append prefixTrace (.next step' (.refl _))⟩
end
end DuplicatePrefix.GeneralBorrowExposedScopedWindowWritableAcceptedCallInput
