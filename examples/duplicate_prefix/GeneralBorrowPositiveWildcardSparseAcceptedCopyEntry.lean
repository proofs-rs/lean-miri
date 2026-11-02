import duplicate_prefix.GeneralBorrowPositiveWildcardSparseAcceptedToCopy
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardSparseAcceptedCopyEntry
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext
open GeneralBorrowExposedScopedWritableAsMutCallReturn
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
/-- Actual original wildcard invocation through len, accepted scalar flow,
mutable expression, as_mut_ptr helper entry/body/release/pop/endCall, pointer
addition and the original ROOT copy-call boundary. -/
theorem invoke (s : GeneralBorrowPositiveWildcardSparseAcceptedInput.Initial) :
    ∃ (updated : Allocation Provenance BorrowTree) (i : GeneralBorrowExposedScopedWritableLenCallInput.Input)
      (stage : GeneralBorrowExposedScopedWritableAcceptedAfterLen.Initial) (expression : GeneralBorrowExposedScopedWritableAcceptedExpression.Input)
      (call : GeneralBorrowExposedScopedWritableAsMutToCopy.Input), ∃ installed,
      GeneralBorrowPositiveWildcardSparseAcceptedAfterLen.Origin s updated i stage ∧
      GeneralBorrowExposedScopedWritableAcceptedAfterLen.Origin stage expression ∧
      GeneralBorrowExposedScopedWritableAcceptedToAsMut.Origin expression call.toInput ∧ call.count=s.count ∧
      Call.initStackFrame (ExecutionMachine.callHooks (config s.options (s.remaining+1) s.span) s.limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
          (Pointer.new .wildcard (Size.ofBytes s.base)) s.len ActualReferenceMetadata.reference).imm,ActualReferenceMetadata.reference⟩,
          .Copy (EmptyRootArguments.second s.count)] false (.memory s.place) (.stop true) ⟨⟨#[]⟩,s.before⟩=.ok () installed ∧
    let cfg:=ActualReferenceContext.config call.options (call.remaining+1) call.span
    let ended:=(GeneralBorrowExposedScopedWritableAsMutCallInput.held call.toInput).global.endCall (({} : FrameState).addProtector call.id call.tracker.global.nextPointerTag)
    let anchor:=GeneralBorrowFreshMetadataChildMutable.index call.data.input
    ∃ root post,
      SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits
        installed (Storage.withCurrent #[] root post) ∧
      PositiveRootSuccessProfile.FrameShape call.caller root (GeneralBorrowExposedScopedWritableAsMutToCopy.scalar call) (GeneralBorrowExposedScopedWritableAsMutToCopy.destinationScalar call) call.count ∧
      post.memory=RetagEntry.updatedMemory call.machine.memory call.id call.entry (released call.toInput) ∧
      post.borrowTracker=some {GeneralBorrowExposedScopedWritableAsMutCallInput.held call.toInput with global:=ended} ∧
      GenericSharedLenAccepted.RuntimeFacts call.options call.remaining call.span call.machine post ∧
      (∃ copy : CopyRootEntry.Input call.options call.limits call.remaining call.span #[] root post (GeneralBorrowExposedScopedWritableAsMutToCopy.scalar call) (GeneralBorrowExposedScopedWritableAsMutToCopy.destinationScalar call) call.count, True) ∧
      ∃ context : GeneralBorrowExposedKnownRootRangeData.Context (released call.toInput) anchor call.selected call.head call.tail,
        GeneralRangeMapOrigins.OwnedOn (fun location=>
          Nonempty (GeneralBorrowExposedScopedWritableReadData.Data (released call.toInput) location ended.protectedTags anchor call.selected call.head call.tail
            (fun position=>call.data.resources.component.support position ∨ position=anchor.toNat) (fun _=>true)) ∧
          Nonempty (GeneralBorrowExposedKnownRootRangeData.Data (released call.toInput) location ended.protectedTags anchor call.selected call.head call.tail .Write) ∧
          Nonempty (GeneralBorrowExposedScopedLeafWriteReadClosed.Data (released call.toInput) location ended.protectedTags anchor call.selected call.head call.tail))
          call.offset (call.offset+call.len) (released call.toInput).locations ∧
        (released call.toInput).locations.WellFormed ∧ (released call.toInput).locations.size=call.entry.allocation.extra.locations.size := by
  obtain ⟨updated,i,stage,expression,call,installed,origin,expressionOrigin,callOrigin,countEq,initialCall,prefixTrace⟩ :=
    GeneralBorrowPositiveWildcardSparseAcceptedToCopy.forms s
  obtain ⟨root,post,helperTrace,rest⟩ := GeneralBorrowExposedScopedWritableAsMutToCopy.executes call
  have options := callOrigin.options.trans (expressionOrigin.options.trans origin.options)
  have limits := callOrigin.limits.trans (expressionOrigin.limits.trans origin.limits)
  have remaining := callOrigin.remaining.trans (expressionOrigin.remaining.trans origin.remaining)
  have span := callOrigin.span.trans (expressionOrigin.span.trans origin.span)
  have actualTrace : SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits installed
      (Storage.withCurrent #[] root post) := by
    rw [options,limits,remaining,span] at helperTrace
    exact SuccessfulTrace.append prefixTrace helperTrace
  exact ⟨updated,i,stage,expression,call,installed,origin,expressionOrigin,callOrigin,countEq,initialCall,root,post,actualTrace,rest⟩
end
end DuplicatePrefix.GeneralBorrowPositiveWildcardSparseAcceptedCopyEntry
