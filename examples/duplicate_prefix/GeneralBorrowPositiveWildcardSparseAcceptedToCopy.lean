import duplicate_prefix.GeneralBorrowPositiveWildcardSparseAcceptedAfterLen
import duplicate_prefix.GeneralBorrowExposedScopedWritableAsMutToCopy
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardSparseAcceptedToCopy
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
/-- Original accepted-call data internally forms the actual mutable helper
call input, including all MIR facts required for its real pointer-add suffix. -/
theorem forms (s : GeneralBorrowPositiveWildcardSparseAcceptedInput.Initial) :
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
      SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits installed
        (Storage.withCurrent #[] call.caller call.machine) := by
  obtain ⟨updated,i,stage,installed,origin,initialCall,initialTrace⟩ := GeneralBorrowPositiveWildcardSparseAcceptedAfterLen.forms s
  obtain ⟨expression,rawCall,expressionOrigin,callOrigin,callTrace⟩ := GeneralBorrowExposedScopedWritableAcceptedCallInput.prepare stage
  have keep (index : Nat) (different : index≠16) : rawCall.caller.locals[index]?=expression.caller.locals[index]? := by
    rw [callOrigin.caller]
    simp [GeneralBorrowExposedScopedWritableAcceptedExpression.expressionFrame,CopyHelperSteps.advance,ActualLocalCopy.written,
      LocalPlaces.cachePlaceLayout,Array.getElem?_set,Ne.symm different]
  have size : rawCall.caller.locals.size=25 := by
    rw [callOrigin.caller]
    simpa only [GeneralBorrowExposedScopedWritableAcceptedExpression.expressionFrame,CopyHelperSteps.advance,ActualLocalCopy.written,
      LocalPlaces.cachePlaceLayout,Array.size_set] using expressionOrigin.frame.size
  have trackNone : rawCall.caller.trackCallerArg=none := by
    rw [callOrigin.caller]
    change expression.caller.trackCallerArg=none
    rw [expressionOrigin.frame.trackCallerArg]
    exact origin.trackNone
  have relevant : 0<rawCall.caller.extra.userRelevance := by
    rw [callOrigin.caller]
    change 0<expression.caller.extra.userRelevance
    rw [expressionOrigin.frame.extra]
    have strong:=UInt8.lt_iff_toNat_lt.mp origin.relevant
    change (64 : Nat)<stage.caller.extra.userRelevance.toNat at strong
    apply UInt8.lt_iff_toNat_lt.mpr
    change (0 : Nat)<stage.caller.extra.userRelevance.toNat
    omega
  have immediate : CopyHelperCleanup.AllImmediate rawCall.caller := by
    rw [callOrigin.caller]
    exact CopyHelperCleanup.all_immediate_written expression.caller 16 ActualReferenceMetadata.reference
      (GeneralBorrowExposedScopedWritableAcceptedExpression.value expression) expression.valid16 expressionOrigin.frame.all
  have slot2 : rawCall.caller.locals[2]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 s.count)))),some RootCompilerFacts.usizeLayout⟩ :=
    (keep 2 (by decide)).trans (expressionOrigin.frame.slot2.trans origin.sourceSlot2)
  have slot13 : rawCall.caller.locals[13]?=some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ :=
    (keep 13 (by decide)).trans expressionOrigin.kept.slot13
  have unused (index : Nat) (low : 17≤index) (high : index≤24) : rawCall.caller.locals[index]?=some ⟨.dead,none⟩ := by
    rw [keep index (by omega),expressionOrigin.kept.high index low]
    exact origin.unused index (by omega) high
  let call : GeneralBorrowExposedScopedWritableAsMutToCopy.Input := {
    toInput:=rawCall,size:=size,trackNone:=trackNone,relevant:=relevant,immediate:=immediate,
    count:=s.count,countPositive:=s.countPositive,within:=by rw [callOrigin.len,expressionOrigin.len,origin.len];exact s.within,
    slot2:=slot2,slot13:=slot13,unused:=unused }
  have trace : SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits
      (Storage.withCurrent #[] stage.caller stage.machine) (Storage.withCurrent #[] call.caller call.machine) := by
    simpa only [origin.options,origin.remaining,origin.span,origin.limits] using callTrace
  exact ⟨updated,i,stage,expression,call,installed,origin,expressionOrigin,callOrigin,rfl,initialCall,SuccessfulTrace.append initialTrace trace⟩
end
end DuplicatePrefix.GeneralBorrowPositiveWildcardSparseAcceptedToCopy
