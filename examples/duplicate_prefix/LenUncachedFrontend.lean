import duplicate_prefix.LenCallFrontend
import duplicate_prefix.CallUncachedLocal
namespace DuplicatePrefix.LenUncachedFrontend
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
open CanonicalConfigFacts
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
def cachedCaller (caller : CompilerFrameContext.ActualFrame) (valid : 11 < caller.locals.size) :=
  LocalPlaces.cachePlaceLayout caller 11 RootCompilerFacts.usizeLayout valid
theorem compute_local11 (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler 11
      (Storage.withCurrent frames frame machine) = .ok RootCompilerFacts.usizeLayout (Storage.withCurrent frames frame machine) := by
  have normalized : CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler frame 11 = .ok 5 := by
    unfold CompilerFrameContext.normalizedLocalType CompilerFrameContext.normalizedBody CompilerFrameContext.bodyOfFrame
    rw [body,identity,callee]
    with_unfolding_all rfl
  unfold CompilerFrameContext.computeLocalLayout
  simp only [MachineHooks.currentFrame,Storage.withCurrent,Stack.currentFrame?,Array.back?_push,
    bind,EStateM.bind,get,getThe,MonadStateOf.get,EStateM.get,pure,EStateM.pure]
  rw [normalized]
  with_unfolding_all change (match PreparedReflection.actual.runtime.lookup 5 with
    | .ok value => EStateM.Result.ok value (Storage.withCurrent frames frame machine)
    | .error error => EStateM.Result.error (StepError.unsupported s!"compiler frame query: {toString error}")
        (Storage.withCurrent frames frame machine)) = _
  rw [RootCompilerFacts.usize_layout_eq]
  rfl
theorem call_uncached_of_entry (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1)
    (span : PreparedContracts.FixedSpanQuery) (debug : options.place.debugAssertions = false)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (value : Immediate Provenance)
    (body : caller.body = RootBody.reflected.body.body)
    (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance)
    (located : caller.location = .mir ⟨2,12⟩)
    (source : PreparedContracts.SourceComparator) (cmp : ProjectionMetadataFacts.NullComparator)
    (validSource : 12 < caller.locals.size)
    (valueSource : caller.locals[12].value = .live (.immediate value))
    (cachedSource : caller.locals[12].layout = some SharedReferenceMetadata.sharedLayout)
    (validDest : 11 < caller.locals.size) (uncachedDest : caller.locals[11].layout = none)
    (noClocks : caller.extra.dataRace = none) (race : machine.dataRace = none)
    (backend : machine.user.payload.payload.user.backend = .none) (ghost : machine.user.payload.ghost = false)
    (afterFrame : CompilerFrameContext.ActualFrame) (afterMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (entry : Call.initStackFrame (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits) ()
      LenHelper.resolved.callee LenHelper.body LenHelper.abi #[.Copy ⟨.immediate value,LenHelper.rawLayout⟩]
      false (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller validDest) 11 RootCompilerFacts.usizeLayout).stackView (.goto (some 3) .Continue)
      (Storage.withCurrent frames (cachedCaller caller validDest) machine) = .ok () (Storage.withCurrent (frames.push (cachedCaller caller validDest)) afterFrame afterMachine)) :
    Call.evalCallTerminator (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits)
      () limits.callDispatch LenCallSource.callTerminator (Storage.withCurrent frames caller machine) =
      .ok () (Storage.withCurrent (frames.push (cachedCaller caller validDest)) afterFrame afterMachine) := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits
  let state := Storage.withCurrent frames caller machine
  let cf := cachedCaller caller validDest
  let cachedState := Storage.withCurrent frames cf machine
  let destination := (LocalPlaces.localRuntimePlace frames.size cf 11 RootCompilerFacts.usizeLayout).stackView
  let after := Storage.withCurrent (frames.push cf) afterFrame afterMachine
  have sourceValid' : 12 < cf.locals.size := by simpa [cf,cachedCaller,LocalPlaces.cachePlaceLayout] using validSource
  have sourceLive' : cf.locals[12].value = .live (.immediate value) := by simpa [cf,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set] using valueSource
  have sourceCached' : cf.locals[12].layout = some SharedReferenceMetadata.sharedLayout := by simpa [cf,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set] using cachedSource
  have evaluated := LenEvaluateCall.evaluate options limits remaining span debug source cmp frames cf machine value
    body identity callee located sourceValid' sourceLive' sourceCached' noClocks ghost
  have dest := CallUncachedLocal.uncached options limits remaining span debug frames caller machine 11
    RootCompilerFacts.usizeLayout validDest uncachedDest (by decide +kernel) (compute_local11 frames caller machine body identity callee)
  have dispatched := LenCallFrontend.dispatch_of_entry options limits remaining budget span cachedState after value destination backend race entry
  have canUnwind : h.abiCanUnwind LenHelper.abi = true := LenCallFacts.abi_flags.2.1
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
    simp [after,Storage.withCurrent,Stack.frameIndex,Array.isEmpty_push,bind,EStateM.bind,
      get,getThe,MonadStateOf.get,EStateM.get,pure,Pure.pure,EStateM.pure,Except.pure]
  apply GenericCallStages.call_terminator h () limits.callDispatch LenCallSource.callTerminator
    LenHelper.resolved.function #[LenEvaluateCall.argument] ⟨11,#[]⟩ 3 .Continue LenCallFrontend.sourceKind LenCallFrontend.fnSpan
    state cachedState cachedState after caller frames.size (frames.size+1) destination
    ⟨.Instance LenHelper.resolved.callee,#[.Copy ⟨.immediate value,LenHelper.rawLayout⟩],.Rust,some LenHelper.abi,false⟩
    LenCallFrontend.source_call (CallEntryLocals.get_frame options limits remaining span frames caller machine) oldIndex dest evaluated
  · simpa only [dispatchFuel,Option.any,canUnwind,ite_true] using dispatched
  · exact newIndex
  · omega
end
end DuplicatePrefix.LenUncachedFrontend
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.LenUncachedFrontend.call_uncached_of_entry) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved len uncached frontend {dependency}"
