import duplicate_prefix.AsMutDispatch
import duplicate_prefix.CallItemDispatch
import duplicate_prefix.AsMutUncachedCall
namespace DuplicatePrefix.GenericAsMutCallFrontend
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
/-- Tree-independent dispatch template, supplied internally with the actual
entry equality by the public successful-invocation theorem. -/
theorem dispatch (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining budget : Nat) (span : PreparedContracts.FixedSpanQuery)
    (state after : CanonicalConfigFacts.RootState) (value : Immediate Provenance)
    (destination : RuntimeStackPlace Provenance)
    (backend : state.machine.user.payload.payload.user.backend = .none) (race : state.machine.dataRace = none)
    (entry : Call.initStackFrame (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      HelperCompilerFacts.asMutPtrCall.callee HelperCompilerFacts.asMutPtrBody HelperCompilerFacts.asMutPtrAbi
      #[.Copy ⟨.immediate value,ActualReferenceMetadata.reference⟩] false destination (.goto (some 7) .Continue) state = .ok () after) :
    Call.initFnCall (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (budget+1) ⟨.Instance HelperCompilerFacts.asMutPtrCall.callee,.Rust,some HelperCompilerFacts.asMutPtrAbi,
        #[.Copy ⟨.immediate value,ActualReferenceMetadata.reference⟩],false,destination,some 7,.Continue⟩ state = .ok () after := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits
  let args : Array (FnArg Provenance) := #[.Copy ⟨.immediate value,ActualReferenceMetadata.reference⟩]
  have find := AsMutDispatch.find_mir options limits (remaining+1) span state args destination (some 7) .Continue backend race
  have rust : h.isRustCall .Rust = false := by
    change (PreparedContracts.actualConfig options () (remaining+1) span).calls.compiler.isRustCall .Rust = false
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).callCompiler]
    rfl
  have kind : HelperCompilerFacts.asMutPtrCall.callee.kind = .Item HelperCompilerFacts.asMutPtrCall.callee.defId := by
    with_unfolding_all rfl
  apply CallItemDispatch.dispatch_one h _ state _ budget
  rw [CallItemDispatch.item_step h HelperCompilerFacts.asMutPtrCall.callee HelperCompilerFacts.asMutPtrCall.callee.defId
    HelperCompilerFacts.asMutPtrAbi args false destination (some 7) .Continue .Rust kind AsMutCallFacts.abi_flags.2.1 rust]
  unfold CallItemDispatch.itemStage
  simp only [bind,EStateM.bind]
  rw [find]
  simp only [bind,EStateM.bind]
  dsimp only [h,args]
  rw [entry]
  rfl

/-- Root call-terminator template including the actual lazy local-15 layout
cache. The source call equality is supplied internally by the final theorem. -/
theorem call_uncached (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (source : PreparedContracts.SourceComparator)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (caller helper : CompilerFrameContext.ActualFrame)
    (machine next : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (value : Immediate Provenance)
    (body : caller.body = RootBody.reflected.body.body)
    (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance)
    (located : caller.location = .mir ⟨6,8⟩)
    (valid16 : (16 : MIR.LocalId) < caller.locals.size)
    (value16 : caller.locals[16].value = .live (.immediate value))
    (cached16 : caller.locals[16].layout = some ActualReferenceMetadata.reference)
    (destValid : (15 : MIR.LocalId) < caller.locals.size) (old : Immediate Provenance)
    (destLive : caller.locals[15].value = .live (.immediate old))
    (uncached : caller.locals[15].layout = none)
    (callerClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (backend : machine.user.payload.payload.user.backend = .none) (race : machine.dataRace = none)
    (entry : Call.initStackFrame (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      HelperCompilerFacts.asMutPtrCall.callee HelperCompilerFacts.asMutPtrBody HelperCompilerFacts.asMutPtrAbi
      #[.Copy ⟨.immediate value,ActualReferenceMetadata.reference⟩] false
      (LocalPlaces.localRuntimePlace 0 (AsMutUncachedCall.cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView
      (.goto (some 7) .Continue) (Storage.withCurrent #[] (AsMutUncachedCall.cachedCaller caller destValid) machine) =
      .ok () (Storage.withCurrent #[AsMutUncachedCall.cachedCaller caller destValid] helper next)) :
    Call.evalCallTerminator (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      () limits.callDispatch AsMutEvaluateCall.terminator (Storage.withCurrent #[] caller machine) =
      .ok () (Storage.withCurrent #[AsMutUncachedCall.cachedCaller caller destValid] helper next) := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits
  let frames : Array CompilerFrameContext.ActualFrame := #[]
  let state := Storage.withCurrent frames caller machine
  let cachedFrame := AsMutUncachedCall.cachedCaller caller destValid
  let cachedState := Storage.withCurrent frames cachedFrame machine
  let destination := (LocalPlaces.localRuntimePlace frames.size cachedFrame 15 CopyCompilerFacts.destPointerLayout).stackView
  let after := Storage.withCurrent #[cachedFrame] helper next
  have valid15' : (15 : MIR.LocalId) < cachedFrame.locals.size := by simpa [cachedFrame,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout] using destValid
  have valid16' : (16 : MIR.LocalId) < cachedFrame.locals.size := by simpa [cachedFrame,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout] using valid16
  have value15' : cachedFrame.locals[15].value = .live (.immediate old) := by
    simpa [cachedFrame,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set_self] using destLive
  have cache15' : cachedFrame.locals[15].layout = some CopyCompilerFacts.destPointerLayout := by
    simp [cachedFrame,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set_self]
  have value16' : cachedFrame.locals[16].value = .live (.immediate value) := by
    simpa [cachedFrame,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set] using value16
  have cache16' : cachedFrame.locals[16].layout = some ActualReferenceMetadata.reference := by
    simpa [cachedFrame,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set] using cached16
  have evaluated := AsMutEvaluateCall.evaluate options limits (remaining+1) span debugOff source cmp frames cachedFrame machine value
    body identity callee located valid16' value16' cache16' callerClocks ghost
  have dest := CallUncachedLocal.uncached options limits (remaining+1) span debugOff frames caller machine 15
    CopyCompilerFacts.destPointerLayout destValid uncached (by decide +kernel) (AsMutUncachedCall.compute_local15 frames caller machine body identity callee)
  have dispatched := dispatch options limits remaining budget span cachedState after value destination backend race entry
  have canUnwind : h.abiCanUnwind HelperCompilerFacts.asMutPtrAbi = true := AsMutCallFacts.abi_flags.2.1
  have oldIndex : h.frameIndex state = .ok frames.size state := by
    change (do match (←get).stack.frameIndex with
      | .ok index => pure index
      | .error error => throw (.stack error) : MachineHooks.M MiriMemoryKind Machine.RootUser Nat) state = _
    simp [state,Storage.withCurrent,Stack.frameIndex,Array.isEmpty_push,bind,EStateM.bind,
      get,getThe,MonadStateOf.get,EStateM.get,pure,Pure.pure,EStateM.pure,Except.pure]
  have newIndex : h.frameIndex after = .ok (frames.size+1) after := by
    change (do match (←get).stack.frameIndex with
      | .ok index => pure index
      | .error error => throw (.stack error) : MachineHooks.M MiriMemoryKind Machine.RootUser Nat) after = _
    simp [after,frames,Storage.withCurrent,Stack.frameIndex,Array.isEmpty_push,bind,EStateM.bind,
      get,getThe,MonadStateOf.get,EStateM.get,pure,Pure.pure,EStateM.pure,Except.pure]
  apply GenericCallStages.call_terminator h () limits.callDispatch AsMutEvaluateCall.terminator
    HelperCompilerFacts.asMutPtrCall.function #[AsMutEvaluateCall.argument] ⟨15,#[]⟩ 7 .Continue AsMutCallTerminator.sourceKind AsMutCallTerminator.fnSpan
    state cachedState cachedState after caller frames.size (frames.size+1) destination
    ⟨.Instance HelperCompilerFacts.asMutPtrCall.callee,#[.Copy ⟨.immediate value,ActualReferenceMetadata.reference⟩],.Rust,some HelperCompilerFacts.asMutPtrAbi,false⟩
    AsMutCallTerminator.source_call (CallEntryLocals.get_frame options limits (remaining+1) span frames caller machine) oldIndex dest evaluated
  · simpa only [dispatchFuel,Option.any,canUnwind,ite_true] using dispatched
  · exact newIndex
  · omega

end
end DuplicatePrefix.GenericAsMutCallFrontend
