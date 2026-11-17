import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableAcceptedAfterLen
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableAcceptedToAsMut
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableAcceptedCallInput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

theorem prepare {profileMode : ProfileMode} (s : GeneralBorrowExposedScopedInactiveWritableAcceptedAfterLen.InitialFor profileMode) :
    ∃ (expression : GeneralBorrowExposedScopedInactiveWritableAcceptedExpression.InputFor profileMode) (call : GeneralBorrowExposedScopedInactiveWritableAsMutCallInput.InputFor profileMode),
      GeneralBorrowExposedScopedInactiveWritableAcceptedAfterLen.Origin s expression ∧
      GeneralBorrowExposedScopedInactiveWritableAcceptedToAsMut.Origin expression call ∧
      SuccessfulTrace.Trace (ActualReferenceContext.config s.options (s.remaining+1) s.span) s.limits
        (Storage.withCurrent #[] s.caller s.machine) (Storage.withCurrent #[] call.caller call.machine) := by
  obtain ⟨expression,origin,prefixTrace⟩:=GeneralBorrowExposedScopedInactiveWritableAcceptedAfterLen.prepare s
  obtain ⟨call,callOrigin,step⟩:=GeneralBorrowExposedScopedInactiveWritableAcceptedToAsMut.forms expression
  have step' : ExecutionMachine.step (ActualReferenceContext.config s.options (s.remaining+1) s.span) s.limits ()
      (Storage.withCurrent #[] expression.caller expression.machine)=(Storage.withCurrent #[] call.caller call.machine,.ok true) := by
    simpa only [origin.options,origin.remaining,origin.span,origin.limits] using step
  exact ⟨expression,call,origin,callOrigin,SuccessfulTrace.append prefixTrace (.next step' (.refl _))⟩
end
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableAcceptedCallInput
