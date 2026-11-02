import duplicate_prefix.GeneralBorrowPositiveConcreteWindowZeroSafety
import duplicate_prefix.GeneralBorrowPositiveConcreteWindowRejectedSafety
import duplicate_prefix.DuplicatePrefixCallResult
namespace DuplicatePrefix.GeneralBorrowPositiveConcreteWindowEarlyCallResult
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open ActualReferenceContext
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
/-- Actual zero-count execution supplies the common call-time result. The
initial contract retains every concrete selected-component restriction. -/
theorem zero {profileMode : ProfileMode} (s : GeneralBorrowPositiveConcreteWindowZero.InitialFor profileMode) :
    DuplicatePrefixCallResult.Result s.options s.limits s.remaining s.span s.before
      (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len s.count s.place := by
  obtain ⟨installed,finalState,call,trace,terminal,empty,safety,reachable⟩ := GeneralBorrowPositiveConcreteWindowZeroSafety.invoke s
  have returned : CallSafety.pastCallBoundary 1 finalState := by
    unfold CallSafety.pastCallBoundary CallSafety.frameDepth
    rw [empty]
    decide
  rw [s.zero]
  exact ⟨installed,finalState,call,trace,terminal,empty,
    SuccessfulTrace.no_errors _ 1 installed finalState safety.1 trace returned,safety,reachable⟩
/-- The actual rejected-count path supplies the same result without entering
the copying branch. No post-operation resource or success certificate is
assumed; inherited initial resource conditions remain explicit. -/
theorem rejected {profileMode : ProfileMode} (s : GeneralBorrowPositiveConcreteWindowRejected.InitialFor profileMode) :
    DuplicatePrefixCallResult.Result s.options s.limits s.remaining s.span s.before
      (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len s.count s.place := by
  obtain ⟨installed,finalState,call,trace,terminal,empty,safety,reachable⟩ := GeneralBorrowPositiveConcreteWindowRejectedSafety.invoke s
  have returned : CallSafety.pastCallBoundary 1 finalState := by
    unfold CallSafety.pastCallBoundary CallSafety.frameDepth
    rw [empty]
    decide
  exact ⟨installed,finalState,call,trace,terminal,empty,
    SuccessfulTrace.no_errors _ 1 installed finalState safety.1 trace returned,safety,reachable⟩
end DuplicatePrefix.GeneralBorrowPositiveConcreteWindowEarlyCallResult
