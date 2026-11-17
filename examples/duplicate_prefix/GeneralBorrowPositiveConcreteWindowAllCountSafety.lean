import duplicate_prefix.GeneralBorrowPositiveConcreteWindowAllCountResult
import duplicate_prefix.GeneralBorrowPositiveConcreteWindowAccepted
import duplicate_prefix.GeneralBorrowPositiveConcreteWindowAcceptedCompleteInput
import duplicate_prefix.GeneralBorrowScopedInactiveWritableRootPhysicalExit
import duplicate_prefix.GeneralBorrowPositiveConcreteWindowOriginalDepth
import duplicate_prefix.SuccessfulTraceTerminal
namespace DuplicatePrefix.GeneralBorrowPositiveConcreteWindowAllCountSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open ActualReferenceContext
variable [area : GeneralBorrowExposedKnownRootState.Scope]
variable {profileMode : ProfileMode}
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Exhaustive count split for the explicit sufficient call-time contract.
No source-history or complete-valid-caller coverage theorem is claimed. -/
theorem invoke (s : GeneralBorrowPositiveConcreteWindowAllCountInput.InitialFor profileMode) :
    GeneralBorrowPositiveConcreteWindowAllCountResult.Result s.toBase := by
  by_cases zero : s.count=0
  · exact GeneralBorrowPositiveConcreteWindowAllCountResult.zero s zero
  · have positive : (0 : UInt64)<s.count:=UInt64.pos_iff_ne_zero.mpr zero
    by_cases within : s.count≤s.len/2
    · let accepted := GeneralBorrowPositiveConcreteWindowAllCountInput.acceptedComplete s positive within
      obtain ⟨input,installed,options,limits,remaining,span,call,prefixTrace⟩ :=
        GeneralBorrowPositiveConcreteWindowAccepted.prepare accepted
      obtain ⟨updated,suffix,terminal,_,_⟩ := GeneralBorrowScopedInactiveWritableRootPhysicalExit.complete input
      rw [options,limits,remaining,span] at suffix terminal
      let finalState := CanonicalCopy.replaceAllocation (GeneralBorrowScopedInactiveWritableRootPhysicalExit.popped input)
        input.release.slotId input.release.slot.kind updated
      have full := SuccessfulTrace.append prefixTrace suffix
      have depth := GeneralBorrowPositiveConcreteWindowOriginalDepth.one accepted.toAccepted.toInitial.toBase installed call
      have entry : CallSafety.IsCallEntry 1 installed := ⟨by decide,depth⟩
      have empty : finalState.stack.frames=#[] := rfl
      have safety := SuccessfulTrace.no_ub
        (⟨config accepted.options (accepted.remaining+1) accepted.span,accepted.limits,fun _ _=>True⟩ :
          CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit)
        1 installed finalState entry full
        (by rw [CallSafety.pastCallBoundary,CallSafety.frameDepth,empty];change (0:Nat)<1;decide)
      exact ⟨installed,finalState,call,full,terminal,empty,SuccessfulTrace.no_errors _ 1 installed finalState safety.1 full (by rw [CallSafety.pastCallBoundary,CallSafety.frameDepth,empty];change (0:Nat)<1;decide),safety,SuccessfulTraceTerminal.prefix_step_success full terminal⟩
    · have outside : s.count>s.len/2:=UInt64.lt_iff_toNat_lt.mpr
        (Nat.lt_of_not_ge (fun bound=>within (UInt64.le_iff_toNat_le.mpr bound)))
      exact GeneralBorrowPositiveConcreteWindowAllCountResult.rejected s outside
end
end DuplicatePrefix.GeneralBorrowPositiveConcreteWindowAllCountSafety
