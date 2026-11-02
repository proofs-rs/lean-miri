import duplicate_prefix.GeneralBorrowPositiveWildcardWindowAllCountInput
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardWindowAllCountResult
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open ActualReferenceContext
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- Original physical call through terminal empty-stack return, with NoUB and
successful steps on every reachable permitted finite Unit-choice prefix. -/
def Result (s : GeneralBorrowPositiveWildcardWindowOriginalInput.Base) : Prop :=
    let cfg := config s.options (s.remaining+1) s.span
    ∃ installed finalState,
      Call.initStackFrame (ExecutionMachine.callHooks cfg s.limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
          (Pointer.new .wildcard (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm,
          ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second s.count)] false (.memory s.place) (.stop true)
        ⟨⟨#[]⟩,s.before⟩ = .ok () installed ∧
      SuccessfulTrace.Trace cfg s.limits installed finalState ∧
      ExecutionMachine.step cfg s.limits () finalState = (finalState,.ok false) ∧
      finalState.stack.frames = #[] ∧
      CallSafety.NoUBBeforeReturn
        (⟨cfg,s.limits,fun _ _ => True⟩ : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit)
        1 installed ∧
      (∀ before, SuccessfulTrace.Trace cfg s.limits installed before →
        ∃ after continuing, ExecutionMachine.step cfg s.limits () before = (after,.ok continuing))

theorem zero (s : GeneralBorrowPositiveWildcardWindowAllCountInput.Initial) (zero : s.count=0) : Result s.toBase := by
  simpa only [Result,GeneralBorrowPositiveWildcardWindowAllCountInput.zero,zero] using GeneralBorrowPositiveWildcardWindowZeroSafety.invoke (GeneralBorrowPositiveWildcardWindowAllCountInput.zero s zero)

theorem rejected (s : GeneralBorrowPositiveWildcardWindowAllCountInput.Initial) (outside : s.count>s.len/2) : Result s.toBase := by
  exact GeneralBorrowPositiveWildcardWindowRejectedSafety.invoke (GeneralBorrowPositiveWildcardWindowAllCountInput.rejected s outside)
end
end DuplicatePrefix.GeneralBorrowPositiveWildcardWindowAllCountResult
