import duplicate_prefix.GeneralBorrowPositiveConcreteWindowAcceptedToCopy
namespace DuplicatePrefix.GeneralBorrowPositiveConcreteWindowAcceptedCopyEntry
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext
open GeneralBorrowExposedScopedInactiveWritableAsMutCallReturn
variable [area : GeneralBorrowExposedKnownRootState.Scope]
variable {profileMode : ProfileMode}
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
/-- Actual original wildcard invocation through len, accepted scalar flow,
mutable expression, as_mut_ptr helper entry/body/release/pop/endCall, pointer
addition and the original ROOT copy-call boundary. -/
theorem invoke (s : GeneralBorrowPositiveConcreteWindowAcceptedInput.InitialFor profileMode) :
    ∃ (updated : Allocation Provenance BorrowTree) (i : GeneralBorrowExposedScopedInactiveWritableLenCallInput.InputFor profileMode)
      (stage : GeneralBorrowExposedScopedInactiveWritableAcceptedAfterLen.InitialFor profileMode) (expression : GeneralBorrowExposedScopedInactiveWritableAcceptedExpression.InputFor profileMode)
      (call : GeneralBorrowExposedScopedInactiveWritableAsMutToCopy.InputFor profileMode), ∃ installed,
      GeneralBorrowPositiveConcreteWindowAcceptedAfterLen.Origin s updated i stage ∧ i.first.offset=s.offset ∧ i.first.len=s.len ∧
      GeneralBorrowExposedScopedInactiveWritableAcceptedAfterLen.Origin stage expression ∧
      GeneralBorrowExposedScopedInactiveWritableAcceptedToAsMut.Origin expression call.toInput ∧ call.count=s.count ∧
      Call.initStackFrame (ExecutionMachine.callHooks (config s.options (s.remaining+1) s.span) s.limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
          (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm,ActualReferenceMetadata.reference⟩,
          .Copy (EmptyRootArguments.second s.count)] false (.memory s.place) (.stop true) ⟨⟨#[]⟩,s.before⟩=.ok () installed ∧
    let cfg:=ActualReferenceContext.config call.options (call.remaining+1) call.span
    let ended:=(GeneralBorrowExposedScopedInactiveWritableAsMutCallInput.held call.toInput).global.endCall (({} : FrameState).addProtector call.id call.tracker.global.nextPointerTag)
    let anchor:=GeneralBorrowFreshMetadataChildMutable.index call.data.input
    ∃ root post,
      SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits
        installed (Storage.withCurrent #[] root post) ∧
      PositiveRootSuccessProfile.FrameShape call.caller root (GeneralBorrowExposedScopedInactiveWritableAsMutToCopy.scalar call) (GeneralBorrowExposedScopedInactiveWritableAsMutToCopy.destinationScalar call) call.count ∧
      post.memory=RetagEntry.updatedMemory call.machine.memory call.id call.entry (released call.toInput) ∧
      post.borrowTracker=some {GeneralBorrowExposedScopedInactiveWritableAsMutCallInput.held call.toInput with global:=ended} ∧
      GenericSharedLenAccepted.RuntimeFacts call.options call.remaining call.span call.machine post ∧
      (∃ copy : CopyRootEntry.Input call.options call.limits call.remaining call.span #[] root post (GeneralBorrowExposedScopedInactiveWritableAsMutToCopy.scalar call) (GeneralBorrowExposedScopedInactiveWritableAsMutToCopy.destinationScalar call) call.count, True) ∧
      ∃ context : GeneralBorrowExposedKnownRootRangeData.Context (released call.toInput) anchor call.selected call.head call.tail,
        GeneralRangeMapOrigins.OwnedOn (fun location=>
          Nonempty (GeneralBorrowExposedScopedInactiveWritableReadData.Data (released call.toInput) location ended.protectedTags anchor call.selected call.head call.tail
            (fun position=>call.data.resources.component.support position ∨ position=anchor.toNat) (fun _=>true)))
          call.offset (call.offset+call.len) (released call.toInput).locations ∧
        (released call.toInput).locations.WellFormed ∧ (released call.toInput).locations.size=call.entry.allocation.extra.locations.size := by
  obtain ⟨updated,i,stage,expression,call,installed,origin,firstOffset,firstLen,expressionOrigin,callOrigin,countEq,initialCall,prefixTrace⟩ :=
    GeneralBorrowPositiveConcreteWindowAcceptedToCopy.forms s
  obtain ⟨root,post,helperTrace,rest⟩ := GeneralBorrowExposedScopedInactiveWritableAsMutToCopy.executes call
  have options := callOrigin.options.trans (expressionOrigin.options.trans origin.options)
  have limits := callOrigin.limits.trans (expressionOrigin.limits.trans origin.limits)
  have remaining := callOrigin.remaining.trans (expressionOrigin.remaining.trans origin.remaining)
  have span := callOrigin.span.trans (expressionOrigin.span.trans origin.span)
  have actualTrace : SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits installed
      (Storage.withCurrent #[] root post) := by
    rw [options,limits,remaining,span] at helperTrace
    exact SuccessfulTrace.append prefixTrace helperTrace
  exact ⟨updated,i,stage,expression,call,installed,origin,firstOffset,firstLen,expressionOrigin,callOrigin,countEq,initialCall,root,post,actualTrace,rest⟩
end
end DuplicatePrefix.GeneralBorrowPositiveConcreteWindowAcceptedCopyEntry
