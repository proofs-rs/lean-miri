import duplicate_prefix.GeneralBorrowForestAsMutAccounting
import duplicate_prefix.GenericAsMutCallFrontend
namespace DuplicatePrefix.GeneralBorrowForestAsMutCallToReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
noncomputable section

set_option autoImplicit false in
/-- Initial caller data. The cached frame is a deterministic view of the same
pre-call locals; the actual lazy layout query runs in the proven source step. -/
structure Input where
  data : GeneralBorrowForestAsMutInvocation.Input
  caller : CompilerFrameContext.ActualFrame
  valid15 : (15 : MIR.LocalId) < caller.locals.size
  cached : data.start.caller = AsMutUncachedCall.cachedCaller caller valid15
  live15 : caller.locals[15].value = .live (.immediate .uninit)
  uncached15 : caller.locals[15].layout = none
  location : caller.location = .mir ⟨6,8⟩
  valid16 : (16 : MIR.LocalId) < caller.locals.size
  value16 : caller.locals[16].value = .live (.immediate (GeneralBorrowForestAsMutInvocationCore.parent data.start))
  cached16 : caller.locals[16].layout = some ActualReferenceMetadata.reference

/-- The actual root MIR call at PC6:8, including terminator accounting, lazy
layout caching, callee evaluation and dispatch, reaches physical true return.
No operation success or post-callee state is an input. -/
theorem complete (input : Input) :
    let s := input.data.start
    let config := PreparedContracts.actualConfig s.options () (s.remaining+1) s.span
    let initial := Storage.withCurrent #[] input.caller s.machine
    ∃ ready : GeneralBorrowForestAsMutPhysicalReturn.Input, ∃ finalState,
      GeneralBorrowForestAsMutPhysicalReturn.Result ready ∧
      SuccessfulTrace.Trace config s.limits initial finalState ∧
      ExecutionMachine.step config s.limits () finalState = (finalState,.ok false) ∧
      finalState.stack.frames = #[] ∧
      CallSafety.NoUBBeforeReturn
        (⟨config,s.limits,fun _ _ => True⟩ : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit)
        1 initial ∧
      (∀ before, SuccessfulTrace.Trace config s.limits initial before →
        ∃ after continuing, ExecutionMachine.step config s.limits () before = (after,.ok continuing)) := by
  let s := input.data.start
  let accounted := GeneralBorrowForestAsMutAccounting.invocation input.data
  let next := AsMutPtrReturn.accountedMachine s.options s.remaining s.span s.machine
  let config := PreparedContracts.actualConfig s.options () (s.remaining+1) s.span
  let initial := Storage.withCurrent #[] input.caller s.machine
  let nextState := Storage.withCurrent #[] input.caller next
  obtain ⟨ready,callerEq,configEq,limitsEq,entry,physical⟩ := GeneralBorrowForestAsMutInvocation.complete_full accounted
  let helper := GeneralBorrowForestAsMutBodyToCopy.helper ready.start
  let after := Storage.withCurrent #[s.caller] helper ready.start.machine
  have cached : s.caller = AsMutUncachedCall.cachedCaller input.caller input.valid15 := input.cached
  have sourceBody : input.caller.body = RootBody.reflected.body.body := by
    have same := s.body
    rw [input.cached] at same
    exact same
  have identity : input.caller.bodyIdentity = RootBody.reflected.body.identity := by
    have same := s.identity
    rw [input.cached] at same
    exact same
  have callee : input.caller.functionInstance = RootBody.reflected.functionInstance := by
    have same := s.callee
    rw [input.cached] at same
    exact same
  have clocks : input.caller.extra.dataRace = none := by
    have same := s.clocks
    rw [input.cached] at same
    exact same
  have nextGhost : next.user.payload.ghost = false := by rw [AsMutPtrReturn.accounted_ghost];exact s.ghost
  have nextBackend : next.user.payload.payload.user.backend = .none := by
    unfold next AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields s.options () (s.remaining+1) s.span).terminators]
    exact s.backend
  have realEntry :
      Call.initStackFrame (ExecutionMachine.callHooks config s.limits) () HelperCompilerFacts.asMutPtrCall.callee
        HelperCompilerFacts.asMutPtrBody HelperCompilerFacts.asMutPtrAbi
        #[.Copy ⟨.immediate (GeneralBorrowForestAsMutInvocationCore.parent s),ActualReferenceMetadata.reference⟩] false
        (LocalPlaces.localRuntimePlace 0 (AsMutUncachedCall.cachedCaller input.caller input.valid15) 15 CopyCompilerFacts.destPointerLayout).stackView
        (.goto (some 7) .Continue) (Storage.withCurrent #[] (AsMutUncachedCall.cachedCaller input.caller input.valid15) next) =
        .ok () (Storage.withCurrent #[AsMutUncachedCall.cachedCaller input.caller input.valid15] helper ready.start.machine) := by
    change Call.initStackFrame (ExecutionMachine.callHooks config s.limits) () HelperCompilerFacts.asMutPtrCall.callee
      HelperCompilerFacts.asMutPtrBody HelperCompilerFacts.asMutPtrAbi
      #[.Copy ⟨.immediate (GeneralBorrowForestAsMutInvocationCore.parent s),ActualReferenceMetadata.reference⟩] false
      (LocalPlaces.localRuntimePlace 0 s.caller 15 CopyCompilerFacts.destPointerLayout).stackView
      (.goto (some 7) .Continue) (Storage.withCurrent #[] s.caller next) = .ok () after at entry
    simpa only [after,cached] using entry
  have call := GenericAsMutCallFrontend.call_uncached s.options s.limits s.remaining s.budget s.dispatch s.span
    s.debug s.source s.cmp input.caller helper next ready.start.machine (GeneralBorrowForestAsMutInvocationCore.parent s)
    sourceBody identity callee input.location input.valid16 input.value16 input.cached16 input.valid15 .uninit input.live15
    input.uncached15 clocks nextGhost nextBackend s.race realEntry
  have effect : Call.evalCallTerminator (ExecutionMachine.callHooks config s.limits) () s.limits.callDispatch
      AsMutEvaluateCall.terminator nextState = .ok () after := by
    simpa only [after,cached] using call
  have accounting := SourceControl.before_terminator config s.limits () initial
    (CanonicalConfigFacts.actual_term_get_set s.options () (s.remaining+1) s.span)
    (CanonicalConfigFacts.actual_term_set_set s.options () (s.remaining+1) s.span) s.unchecked s.noGc s.fixed
  have accounting' : (ExecutionMachine.stepHooks config s.limits).beforeTerminator () initial = (nextState,.ok ()) := accounting
  let block := RootBody.reflected.body.body.basicBlocks[6]'(by decide +kernel)
  have blockAt : input.caller.body.basicBlocks[6]? = some block := by rw [sourceBody];simp [block]
  have noStatement : block.statements[8]? = none := by with_unfolding_all rfl
  have first : ExecutionMachine.step config s.limits () initial = (after,.ok true) := by
    apply GenericCallStages.source_step config s.limits () initial nextState after input.caller ⟨6,8⟩ block
      HelperCompilerFacts.asMutPtrCall.function #[AsMutEvaluateCall.argument] ⟨15,#[]⟩ (some 7) .Continue
      AsMutCallTerminator.sourceKind AsMutCallTerminator.fnSpan
      (by simp [initial,Storage.withCurrent,Stack.currentFrame?]) input.location blockAt noStatement
      AsMutCallTerminator.source_call accounting' effect
    change 2 ≠ 1
    decide
  have physicalFull := physical
  obtain ⟨finalState,updated,trace,terminal,empty,rest⟩ := physical
  have readyConfig : PreparedContracts.actualConfig ready.start.options () (ready.start.remaining+1) ready.start.span = config := by
    exact configEq.trans rfl
  have readyLimits : ready.start.limits = s.limits := limitsEq
  rw [readyConfig,readyLimits] at trace terminal
  have readyCaller : ready.start.caller = s.caller := callerEq
  have tail : SuccessfulTrace.Trace config s.limits after finalState := by
    simpa only [after,helper,readyCaller] using trace
  have full : SuccessfulTrace.Trace config s.limits initial finalState := .next first tail
  have safety := SuccessfulTrace.no_ub
    (⟨config,s.limits,fun _ _ => True⟩ : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit)
    1 initial finalState ⟨by decide,rfl⟩ full (by rw [CallSafety.pastCallBoundary,CallSafety.frameDepth,empty];change 0 < 1;decide)
  exact ⟨ready,finalState,physicalFull,full,terminal,empty,safety,
    SuccessfulTraceTerminal.prefix_step_success full terminal⟩
end
end DuplicatePrefix.GeneralBorrowForestAsMutCallToReturn
