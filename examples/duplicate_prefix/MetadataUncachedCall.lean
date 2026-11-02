import duplicate_prefix.MetadataCallTerminator
import duplicate_prefix.CallUncachedLocal
namespace DuplicatePrefix.MetadataUncachedCall
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
open CanonicalConfigFacts MetadataEntry MetadataCallTerminator
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def cachedCaller (frame : CompilerFrameContext.ActualFrame) (valid : 0 < frame.locals.size) :=
  LocalPlaces.cachePlaceLayout frame 0 RootCompilerFacts.usizeLayout valid

theorem compute_local0 (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = HelperCompilerFacts.lenBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.lenBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.lenCall.callee) :
    CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler 0
      (Storage.withCurrent frames frame machine) = .ok RootCompilerFacts.usizeLayout (Storage.withCurrent frames frame machine) := by
  have normalized : CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler frame 0 = .ok 5 := by
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
theorem call_uncached (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining budget : Nat)
    (dispatchFuel : limits.callDispatch = budget+1) (span : PreparedContracts.FixedSpanQuery) (debug : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (carrier : Pointer Provenance ⊕ UInt64) (len : UInt64)
    (body : caller.body = HelperCompilerFacts.lenBody.body)
    (identity : caller.bodyIdentity = HelperCompilerFacts.lenBody.identity)
    (callee : caller.functionInstance = HelperCompilerFacts.lenCall.callee)
    (located : caller.location = .mir ⟨0,2⟩)
    (source : PreparedContracts.SourceComparator) (cmp : ProjectionMetadataFacts.NullComparator)
    (valid2 : 2 < caller.locals.size)
    (value2 : caller.locals[2].value = .live (.immediate (PtrMetadataComplete.rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len)))
    (cached2 : caller.locals[2].layout = some PtrMetadataHelper.rawLayout)
    (valid : 0 < caller.locals.size) (old : Immediate Provenance)
    (live : caller.locals[0].value = .live (.immediate old))
    (uncached : caller.locals[0].layout = none)
    (noClocks : caller.extra.dataRace = none) (noRace : machine.dataRace = none)
    (backend : machine.user.payload.payload.user.backend = .none)
    (fuel : Nat) (validationFuel : options.limits.validation = fuel+1)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat)
    (current : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (MetadataPush.pushed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller valid) machine)
      (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 0 RootCompilerFacts.usizeLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (present : (MetadataPush.pushed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller valid) machine)
      (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 0 RootCompilerFacts.usizeLayout).stackView).stack.frames[index]? = some current) :
    Call.evalCallTerminator (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      () limits.callDispatch SliceLenFacts.callTerminator
      (Storage.withCurrent frames caller machine) =
      .ok () (Storage.withCurrent (frames.push (cachedCaller caller valid))
        (initialized options (Storage.withCurrent frames (cachedCaller caller valid) machine)
          (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 0 RootCompilerFacts.usizeLayout).stackView
          (PtrMetadataComplete.rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len))
        (MetadataPush.completed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller valid) machine)
          (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 0 RootCompilerFacts.usizeLayout).stackView current).machine) := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits
  let state := Storage.withCurrent frames caller machine
  let cachedFrame := cachedCaller caller valid
  let cachedState := Storage.withCurrent frames cachedFrame machine
  let destination := (LocalPlaces.localRuntimePlace frames.size cachedFrame 0 RootCompilerFacts.usizeLayout).stackView
  let value := PtrMetadataComplete.rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len
  let after := Storage.withCurrent (frames.push cachedFrame) (initialized options cachedState destination value)
    (MetadataPush.completed options.userRelevantCrates cachedState destination current).machine
  have valid2' : 2 < cachedFrame.locals.size := by simpa [cachedFrame,cachedCaller,LocalPlaces.cachePlaceLayout] using valid2
  have valid0' : 0 < cachedFrame.locals.size := by simpa [cachedFrame,cachedCaller,LocalPlaces.cachePlaceLayout] using valid
  have value2' : cachedFrame.locals[2].value = .live (.immediate value) := by
    simpa [cachedFrame,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set,value] using value2
  have cached2' : cachedFrame.locals[2].layout = some PtrMetadataHelper.rawLayout := by
    simpa [cachedFrame,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set] using cached2
  have value0' : cachedFrame.locals[0].value = .live (.immediate old) := by
    simpa [cachedFrame,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set_self] using live
  have cached0' : cachedFrame.locals[0].layout = some RootCompilerFacts.usizeLayout := by
    simp [cachedFrame,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set_self]
  have evaluated := MetadataEvaluateCall.evaluate options limits (remaining+1) span debug source cmp frames cachedFrame machine value
    body identity callee located valid2' value2' cached2' noClocks ghost
  have dest := CallUncachedLocal.uncached options limits (remaining+1) span debug frames caller machine 0
    RootCompilerFacts.usizeLayout valid uncached (by decide +kernel) (compute_local0 frames caller machine body identity callee)
  have dispatched := MetadataDispatchEntry.actual_dispatch options limits remaining budget span debug frames cachedFrame machine tracker tracked
    carrier len valid0' old value0' cached0' noClocks noRace backend fuel validationFuel ghost shallow thread index current active top present
  have canUnwind : h.abiCanUnwind PtrMetadataHelper.abi = true := MetadataCallFacts.abi_flags.2.1
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
  apply GenericCallStages.call_terminator h () limits.callDispatch SliceLenFacts.callTerminator
    PtrMetadataHelper.resolved.function #[MetadataEvaluateCall.argument] ⟨0,#[]⟩ 1 .Continue sourceKind fnSpan
    state cachedState cachedState after caller frames.size (frames.size+1) destination
    ⟨.Instance PtrMetadataHelper.resolved.callee,#[.Copy ⟨.immediate value,PtrMetadataHelper.rawLayout⟩],.Rust,some PtrMetadataHelper.abi,false⟩
    source_call (CallEntryLocals.get_frame options limits (remaining+1) span frames caller machine) oldIndex dest evaluated
  · simpa only [dispatchFuel,Option.any,canUnwind,ite_true] using dispatched
  · exact newIndex
  · omega
end
end DuplicatePrefix.MetadataUncachedCall
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.MetadataUncachedCall.call_uncached) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved uncached metadata call dependency {dependency}"
