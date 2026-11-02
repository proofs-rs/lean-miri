import duplicate_prefix.DuplicatePrefixCallResult
import duplicate_prefix.GeneralBorrowPositiveWildcardWindowAllCountSafety
namespace DuplicatePrefix.DuplicatePrefixWindowCallResult
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
variable [area : GeneralBorrowExposedKnownRootState.Scope]
noncomputable section
/-- The existing window theorem proves the same call-time postcondition.
All leaf, permission, allocator, runtime and resource restrictions of Initial
remain visible. No source-history witness is an argument. -/
theorem window (s : GeneralBorrowPositiveWildcardWindowAllCountInput.Initial) :
    DuplicatePrefixCallResult.Result s.options s.limits s.remaining s.span s.before
      (Pointer.new .wildcard (Size.ofBytes (s.base+s.offset))) s.len s.count s.place := by
  obtain ⟨installed,finalState,call,trace,terminal,empty,safety,reachableState⟩ :=
    GeneralBorrowPositiveWildcardWindowAllCountSafety.invoke s
  have returned : CallSafety.pastCallBoundary 1 finalState := by
    unfold CallSafety.pastCallBoundary CallSafety.frameDepth
    rw [empty]
    decide
  exact ⟨installed,finalState,call,trace,terminal,empty,
    SuccessfulTrace.no_errors _ 1 installed finalState safety.1 trace returned,safety,reachableState⟩
end
end DuplicatePrefix.DuplicatePrefixWindowCallResult
