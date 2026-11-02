import duplicate_prefix.GeneralBorrowPositiveConcreteWindowAcceptedCompleteInput
import duplicate_prefix.GeneralBorrowPositiveConcreteWindowAllCountResult
import duplicate_prefix.GeneralBorrowScopedInactiveWritableRootPhysicalExit
import duplicate_prefix.GeneralBorrowPositiveConcreteWindowOriginalDepth
import duplicate_prefix.SuccessfulTraceTerminal
namespace DuplicatePrefix.GeneralBorrowPositiveConcreteWindowAcceptedFinish
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open ActualReferenceContext
variable [area : GeneralBorrowExposedKnownRootState.Scope]
variable {profileMode : ProfileMode}
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
/-- Compose a source-derived physical exit plan with the original invocation.
The exit theorem derives the actual release, return, and terminal step. -/
theorem finish (s : GeneralBorrowPositiveConcreteWindowAcceptedCompleteInput.InitialFor profileMode)
    (installed : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (input : GeneralBorrowScopedInactiveWritableRootPhysicalExit.Input)
    (options : input.options=s.options) (limits : input.limits=s.limits)
    (remaining : input.remaining=s.remaining) (span : input.span=s.span)
    (call : Call.initStackFrame (ExecutionMachine.callHooks (config s.options (s.remaining+1) s.span) s.limits) ()
      RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
        (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm,ActualReferenceMetadata.reference⟩,
        .Copy (EmptyRootArguments.second s.count)] false (.memory s.place) (.stop true)
      ⟨⟨#[]⟩,s.before⟩=.ok () installed)
    (prefixTrace : SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits installed
      (Storage.withCurrent #[] (GeneralBorrowScopedInactiveWritableRootPhysicalExit.caller input) input.machine)) :
    GeneralBorrowPositiveConcreteWindowAllCountResult.Result s.toAccepted.toInitial.toBase := by
  obtain ⟨updated,suffix,terminal,_,_⟩ := GeneralBorrowScopedInactiveWritableRootPhysicalExit.complete input
  rw [options,limits,remaining,span] at suffix terminal
  let finalState := CanonicalCopy.replaceAllocation (GeneralBorrowScopedInactiveWritableRootPhysicalExit.popped input)
    input.release.slotId input.release.slot.kind updated
  have full := SuccessfulTrace.append prefixTrace suffix
  have depth := GeneralBorrowPositiveConcreteWindowOriginalDepth.one s.toAccepted.toInitial.toBase installed call
  have entry : CallSafety.IsCallEntry 1 installed := ⟨by decide,depth⟩
  have empty : finalState.stack.frames=#[] := rfl
  have safety := SuccessfulTrace.no_ub
    (⟨config s.options (s.remaining+1) s.span,s.limits,fun _ _=>True⟩ :
      CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit)
    1 installed finalState entry full
    (by rw [CallSafety.pastCallBoundary,CallSafety.frameDepth,empty];change (0:Nat)<1;decide)
  exact ⟨installed,finalState,call,full,terminal,empty,SuccessfulTrace.no_errors _ 1 installed finalState safety.1 full (by rw [CallSafety.pastCallBoundary,CallSafety.frameDepth,empty];change (0:Nat)<1;decide),safety,SuccessfulTraceTerminal.prefix_step_success full terminal⟩
end DuplicatePrefix.GeneralBorrowPositiveConcreteWindowAcceptedFinish
