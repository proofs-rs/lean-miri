import duplicate_prefix.GeneralBorrowPositiveWildcardRejected
import duplicate_prefix.SuccessfulTraceTerminal
import duplicate_prefix.GeneralBorrowPositiveWildcardOriginalDepth

namespace DuplicatePrefix.GeneralBorrowPositiveWildcardRejectedSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open ActualReferenceContext
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

/-- Genuine original ROOT call, physical false return and finite-prefix NoUB
for count>len/2 on a positive wildcard slice with exposed old roots. All
configuration, physical memory, initial exposed-leaf/scoped allocator and
fresh-tag assumptions are the explicit INITIAL caller contract. This does not
claim the accepted count cases or arbitrary-history formation. -/
theorem invoke (s : GeneralBorrowPositiveWildcardRejected.Initial) :
    let cfg := config s.options (s.remaining+1) s.span
    ∃ installed finalState,
      Call.initStackFrame (ExecutionMachine.callHooks cfg s.limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
          (Pointer.new .wildcard (Size.ofBytes s.base)) s.len ActualReferenceMetadata.reference).imm,
          ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second s.count)] false (.memory s.place) (.stop true)
        ⟨⟨#[]⟩,s.before⟩ = .ok () installed ∧
      SuccessfulTrace.Trace cfg s.limits installed finalState ∧
      ExecutionMachine.step cfg s.limits () finalState = (finalState,.ok false) ∧
      finalState.stack.frames = #[] ∧
      CallSafety.NoUBBeforeReturn
        (⟨cfg,s.limits,fun _ _ => True⟩ : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit)
        1 installed ∧
      (∀ before, SuccessfulTrace.Trace cfg s.limits installed before →
        ∃ after continuing, ExecutionMachine.step cfg s.limits () before = (after,.ok continuing)) := by
  obtain ⟨input,installed,optionsEq,limitsEq,remainingEq,spanEq,call,prefixTrace⟩ := GeneralBorrowPositiveWildcardRejected.prepare s
  obtain ⟨updated,suffix,terminal,_,_⟩ := GeneralBorrowScopedDualRootRejectedPhysical.complete input
  rw [optionsEq,limitsEq,remainingEq,spanEq] at suffix terminal
  let finalState := CanonicalCopy.replaceAllocation (GeneralBorrowScopedDualRootRejectedPhysical.popped input)
    input.release.slotId input.release.slot.kind updated
  have full := SuccessfulTrace.append prefixTrace suffix
  have depth := GeneralBorrowPositiveWildcardOriginalDepth.one s.toInitial.toBase installed call
  have entry : CallSafety.IsCallEntry 1 installed := ⟨by decide,depth⟩
  have empty : finalState.stack.frames=#[] := rfl
  have safety := SuccessfulTrace.no_ub
    (⟨config s.options (s.remaining+1) s.span,s.limits,fun _ _ => True⟩ :
      CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit)
    1 installed finalState entry full
    (by rw [CallSafety.pastCallBoundary,CallSafety.frameDepth,empty];change (0:Nat)<1;decide)
  exact ⟨installed,finalState,call,full,terminal,empty,safety,SuccessfulTraceTerminal.prefix_step_success full terminal⟩

end DuplicatePrefix.GeneralBorrowPositiveWildcardRejectedSafety
