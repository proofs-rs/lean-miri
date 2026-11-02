import duplicate_prefix.GeneralBorrowForestFunctionEntryZero
import duplicate_prefix.SuccessfulTraceTerminal

namespace DuplicatePrefix.GeneralBorrowForestZeroSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open ActualReferenceContext
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

/-- Genuine original ROOT call, physical true return and finite-prefix NoUB
for count ZERO on a positive slice in a general multiple-root forest. All
configuration, physical memory, region/cache/ownership, selected-slot Clean and
fresh-tag assumptions are the explicit INITIAL caller contract. This does not
claim the nonzero count cases or arbitrary-history formation. -/
theorem invoke (s : GeneralBorrowForestFunctionEntryZero.Initial) :
    let cfg := config s.options (s.remaining+1) s.span
    ∃ installed finalState,
      Call.initStackFrame (ExecutionMachine.callHooks cfg s.limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
          (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm,
          ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second 0)] false (.memory s.place) (.stop true)
        ⟨⟨#[]⟩,s.before⟩ = .ok () installed ∧
      SuccessfulTrace.Trace cfg s.limits installed finalState ∧
      ExecutionMachine.step cfg s.limits () finalState = (finalState,.ok false) ∧
      finalState.stack.frames = #[] ∧
      CallSafety.NoUBBeforeReturn
        (⟨cfg,s.limits,fun _ _ => True⟩ : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit)
        1 installed ∧
      (∀ before, SuccessfulTrace.Trace cfg s.limits installed before →
        ∃ after continuing, ExecutionMachine.step cfg s.limits () before = (after,.ok continuing)) := by
  obtain ⟨input,optionsEq,limitsEq,remainingEq,spanEq,call,physical⟩ := GeneralBorrowForestFunctionEntryZero.invoke s
  obtain ⟨updated,trace,terminal,safety,_⟩ := physical
  let installed := Storage.withCurrent #[] input.before input.machine
  let finalState := CanonicalCopy.replaceAllocation (GeneralBorrowForestRootZeroPhysical.popped input)
    input.release.slotId input.release.slot.kind updated
  rw [optionsEq,limitsEq,remainingEq,spanEq] at trace terminal safety
  exact ⟨installed,finalState,call,trace,terminal,rfl,safety,SuccessfulTraceTerminal.prefix_step_success trace terminal⟩

end DuplicatePrefix.GeneralBorrowForestZeroSafety
