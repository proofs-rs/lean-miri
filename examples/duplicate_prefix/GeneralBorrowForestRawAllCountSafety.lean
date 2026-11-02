import duplicate_prefix.GeneralBorrowForestRawAllCountInput
namespace DuplicatePrefix.GeneralBorrowForestRawAllCountSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open ActualReferenceContext
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
def Result (s : GeneralBorrowForestRawAllCountInput.Initial) : Prop :=
  let cfg := config s.options (s.remaining+1) s.span
  ∃ installed finalState,
    Call.initStackFrame (ExecutionMachine.callHooks cfg s.limits) ()
      RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
        (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm,
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

/-- The actual arbitrary-count physical root invocation from one original
high-water caller contract. Future allocations and helper protector flags are
formed internally. Positive slice length and the retained original physical,
compiler, forest and byte-validity conditions remain explicit. -/
theorem invoke (s : GeneralBorrowForestRawAllCountInput.Initial) : Result s :=
  GeneralBorrowForestAllCountSafety.invoke (GeneralBorrowForestRawAllCountInput.toInitial s)
end
end DuplicatePrefix.GeneralBorrowForestRawAllCountSafety
