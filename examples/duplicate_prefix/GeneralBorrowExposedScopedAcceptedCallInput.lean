import duplicate_prefix.GeneralBorrowExposedScopedAcceptedAfterLen
import duplicate_prefix.GeneralBorrowExposedScopedAcceptedToAsMut
namespace DuplicatePrefix.GeneralBorrowExposedScopedAcceptedCallInput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

theorem prepare (s : GeneralBorrowExposedScopedAcceptedAfterLen.Initial) :
    ∃ (expression : GeneralBorrowExposedScopedAcceptedExpression.Input) (call : GeneralBorrowExposedScopedAsMutCallInput.Input),
      GeneralBorrowExposedScopedAcceptedAfterLen.Origin s expression ∧
      GeneralBorrowExposedScopedAcceptedToAsMut.Origin expression call ∧
      SuccessfulTrace.Trace (ActualReferenceContext.config s.options (s.remaining+1) s.span) s.limits
        (Storage.withCurrent #[] s.caller s.machine) (Storage.withCurrent #[] call.caller call.machine) := by
  obtain ⟨expression,origin,prefixTrace⟩:=GeneralBorrowExposedScopedAcceptedAfterLen.prepare s
  obtain ⟨call,callOrigin,step⟩:=GeneralBorrowExposedScopedAcceptedToAsMut.forms expression
  have step' : ExecutionMachine.step (ActualReferenceContext.config s.options (s.remaining+1) s.span) s.limits ()
      (Storage.withCurrent #[] expression.caller expression.machine)=(Storage.withCurrent #[] call.caller call.machine,.ok true) := by
    simpa only [origin.options,origin.remaining,origin.span,origin.limits] using step
  exact ⟨expression,call,origin,callOrigin,SuccessfulTrace.append prefixTrace (.next step' (.refl _))⟩
end
end DuplicatePrefix.GeneralBorrowExposedScopedAcceptedCallInput
