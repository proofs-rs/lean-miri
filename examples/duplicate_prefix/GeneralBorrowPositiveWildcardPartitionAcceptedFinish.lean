import duplicate_prefix.GeneralBorrowPositiveWildcardPartitionAcceptedCompleteInput
import duplicate_prefix.GeneralBorrowPositiveWildcardPartitionAllCountResult
import duplicate_prefix.GeneralBorrowScopedDualRootPhysicalExit
import duplicate_prefix.GeneralBorrowPositiveWildcardPartitionOriginalDepth
import duplicate_prefix.SuccessfulTraceTerminal
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardPartitionAcceptedFinish
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open ActualReferenceContext
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
/-- Compose a source-derived physical exit plan with the original invocation.
The exit theorem derives the actual release, return, and terminal step. -/
theorem finish (s : GeneralBorrowPositiveWildcardPartitionAcceptedCompleteInput.Initial)
    (installed : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (input : GeneralBorrowScopedDualRootPhysicalExit.Input)
    (options : input.options=s.options) (limits : input.limits=s.limits)
    (remaining : input.remaining=s.remaining) (span : input.span=s.span)
    (call : Call.initStackFrame (ExecutionMachine.callHooks (config s.options (s.remaining+1) s.span) s.limits) ()
      RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
        (Pointer.new .wildcard (Size.ofBytes s.base)) s.len ActualReferenceMetadata.reference).imm,ActualReferenceMetadata.reference⟩,
        .Copy (EmptyRootArguments.second s.count)] false (.memory s.place) (.stop true)
      ⟨⟨#[]⟩,s.before⟩=.ok () installed)
    (prefixTrace : SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits installed
      (Storage.withCurrent #[] (GeneralBorrowScopedDualRootPhysicalExit.caller input) input.machine)) :
    GeneralBorrowPositiveWildcardPartitionAllCountResult.Result s.toAccepted.toInitial.toBase := by
  obtain ⟨updated,suffix,terminal,_,_⟩ := GeneralBorrowScopedDualRootPhysicalExit.complete input
  rw [options,limits,remaining,span] at suffix terminal
  let finalState := CanonicalCopy.replaceAllocation (GeneralBorrowScopedDualRootPhysicalExit.popped input)
    input.release.slotId input.release.slot.kind updated
  have full := SuccessfulTrace.append prefixTrace suffix
  have depth := GeneralBorrowPositiveWildcardPartitionOriginalDepth.one s.toAccepted.toInitial.toBase installed call
  have entry : CallSafety.IsCallEntry 1 installed := ⟨by decide,depth⟩
  have empty : finalState.stack.frames=#[] := rfl
  have safety := SuccessfulTrace.no_ub
    (⟨config s.options (s.remaining+1) s.span,s.limits,fun _ _=>True⟩ :
      CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit)
    1 installed finalState entry full
    (by rw [CallSafety.pastCallBoundary,CallSafety.frameDepth,empty];change (0:Nat)<1;decide)
  exact ⟨installed,finalState,call,full,terminal,empty,safety,SuccessfulTraceTerminal.prefix_step_success full terminal⟩
end DuplicatePrefix.GeneralBorrowPositiveWildcardPartitionAcceptedFinish
