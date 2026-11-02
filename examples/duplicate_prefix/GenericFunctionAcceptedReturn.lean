import duplicate_prefix.GenericFunctionEntryAccepted
import duplicate_prefix.GenericSharedAcceptedReturn

namespace DuplicatePrefix.GenericFunctionAcceptedReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open ActualReferenceContext
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

set_option autoImplicit false in
/-- The single-root append-only positive accepted invocation, starting at its
actual original ROOT call. All input assumptions precede call initialization;
no successful operation, intermediate state or safety certificate is assumed. -/
theorem invoke {reuse : Bool} (s : GenericFunctionEntryAccepted.Initial reuse) :
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
        ∃ after continuing, ExecutionMachine.step cfg s.limits () before = (after,.ok continuing)) := by
  obtain ⟨input,optionsEq,limitsEq,remainingEq,spanEq,_,_,_,installed,call,leadingTrace,depth⟩ :=
    GenericFunctionEntryAccepted.prepare s
  obtain ⟨ready,finalState,physical,suffix,terminal,empty,_,_⟩ :=
    GenericSharedAcceptedReturn.complete input
  rw [optionsEq,limitsEq,remainingEq,spanEq] at suffix terminal
  have full := SuccessfulTrace.append leadingTrace suffix
  have entry : CallSafety.IsCallEntry 1 installed := ⟨by decide,depth⟩
  have safety := SuccessfulTrace.no_ub
    (⟨config s.options (s.remaining+1) s.span,s.limits,fun _ _ => True⟩ :
      CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit)
    1 installed finalState entry full
    (by rw [CallSafety.pastCallBoundary,CallSafety.frameDepth,empty];change 0 < 1;decide)
  exact ⟨installed,finalState,call,full,terminal,empty,safety,
    SuccessfulTraceTerminal.prefix_step_success full terminal⟩

end DuplicatePrefix.GenericFunctionAcceptedReturn
