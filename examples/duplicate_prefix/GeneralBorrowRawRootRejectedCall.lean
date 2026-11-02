import duplicate_prefix.GeneralBorrowRawRootRejectedInvoke
namespace DuplicatePrefix.GeneralBorrowRawRootRejectedCall
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
open CanonicalConfigFacts ActualReferenceContext GenericFunctionEntryState
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section
abbrev Initial := GeneralBorrowRawRootZeroEntry.Initial
 theorem invoke (s : Initial) (n : UInt64) (positiveCount : n ≠ 0) (rejected : n > s.len/2)
    (preciseOff : s.options.retag.preciseInteriorMut = false)
    (implicitOff : s.options.retag.implicitWrites = false)
    (budget : Nat) (dispatch : s.limits.callDispatch = budget+1)
    (nodeMargin : s.entry.allocation.extra.nodes.size+3 < 65536)
    (tagMargin : s.tracker.global.nextPointerTag.value.toNat+3 < 18446744073709551615) :
    ∃ prepared : GeneralBorrowRawRootRejectedInvoke.Prepared s n,
      ∃ result : GeneralBorrowRawRootCurrentBoolReturn.Outcome prepared.current,
      ∃ final,
      SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits
        (Storage.withCurrent #[] prepared.entry prepared.initial) final ∧
      CallSafety.NoErrorsBeforeReturn ⟨config s.options (s.remaining+1) s.span,s.limits,fun _ _ => True⟩ 1
        (Storage.withCurrent #[] prepared.entry prepared.initial) ∧
      CallSafety.NoUBBeforeReturn ⟨config s.options (s.remaining+1) s.span,s.limits,fun _ _ => True⟩ 1
        (Storage.withCurrent #[] prepared.entry prepared.initial) ∧
      ExecutionMachine.step (config s.options (s.remaining+1) s.span) s.limits () final = (final,.ok false) ∧
      result.physical.value = false := by
  obtain ⟨prepared⟩ := GeneralBorrowRawRootRejectedInvoke.prepare s n positiveCount rejected preciseOff implicitOff budget dispatch nodeMargin tagMargin
  obtain ⟨result⟩ := GeneralBorrowRawRootCurrentBoolReturn.complete prepared.current
  obtain ⟨updated,exitTrace,terminal,_,rest⟩ := result.returned
  let final := CanonicalCopy.replaceAllocation (GeneralBorrowRawRootBoolReturn.popped result.physical)
    result.physical.release.slotId result.physical.release.slot.kind updated
  have exit : SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits
      (Storage.withCurrent #[] prepared.current.before prepared.current.machine) final := by
    simpa only [GeneralBorrowRawRootBoolReturn.caller,result.options,prepared.options,result.remaining,prepared.remaining,
      result.span,prepared.span,result.limits,prepared.limits,result.before,result.machine] using exitTrace
  have trace := SuccessfulTrace.append prepared.trace exit
  have entry : CallSafety.IsCallEntry 1 (Storage.withCurrent #[] prepared.entry prepared.initial) := by
    exact ⟨by decide, rfl⟩
  have returned : CallSafety.pastCallBoundary 1 final := by
    change 0 < 1
    decide
  refine ⟨prepared,result,final,trace,SuccessfulTrace.no_errors _ 1 _ _ entry trace returned,
    SuccessfulTrace.no_ub _ 1 _ _ entry trace returned,?_,result.value.trans prepared.value⟩
  simpa only [result.options,prepared.options,result.remaining,prepared.remaining,result.span,prepared.span,
    result.limits,prepared.limits] using terminal
end
end DuplicatePrefix.GeneralBorrowRawRootRejectedCall
