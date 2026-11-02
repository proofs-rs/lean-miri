import duplicate_prefix.CopyCallTerminator
import duplicate_prefix.CallUncachedLocal
namespace DuplicatePrefix.CopyUncachedCall
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CanonicalConfigFacts CopyEntry CopyCallTerminator
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable def cachedCaller (caller : CompilerFrameContext.ActualFrame) (valid : 18 < caller.locals.size) :=
  LocalPlaces.cachePlaceLayout caller 18 CopyHelperUnit.layout valid
 theorem compute_local18 (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : caller.body = RootBody.reflected.body.body) (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance) :
    CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler 18 (Storage.withCurrent frames caller machine) =
      .ok CopyHelperUnit.layout (Storage.withCurrent frames caller machine) := by
  have normalized : CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler caller 18 = .ok 2 := by
    unfold CompilerFrameContext.normalizedLocalType CompilerFrameContext.normalizedBody CompilerFrameContext.bodyOfFrame
    rw [body,identity,callee]
    with_unfolding_all rfl
  unfold CompilerFrameContext.computeLocalLayout
  simp only [MachineHooks.currentFrame,Storage.withCurrent,Stack.currentFrame?,Array.back?_push,
    bind,EStateM.bind,get,getThe,MonadStateOf.get,EStateM.get,pure,EStateM.pure]
  rw [normalized]
  with_unfolding_all change (match PreparedReflection.actual.runtime.lookup 2 with
    | .ok value => EStateM.Result.ok value (Storage.withCurrent frames caller machine)
    | .error error => EStateM.Result.error (StepError.unsupported s!"compiler frame query: {toString error}")
        (Storage.withCurrent frames caller machine)) = _
  rw [CopyHelperUnit.layout_query]
  rfl
 theorem call_uncached (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (debug : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (sourcePointer destinationPointer : Scalar Provenance) (n : UInt64) (valid : 18 < caller.locals.size)
    (old : Immediate Provenance) (live : caller.locals[18].value = .live (.immediate old))
    (uncached : caller.locals[18].layout = none)
    (noClocks : caller.extra.dataRace = none) (noRace : machine.dataRace = none)
    (body : caller.body = RootBody.reflected.body.body) (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance) (trackNone : caller.trackCallerArg = none)
    (location : caller.location = .mir ⟨8,RootCallerLocation.statementCount 8⟩)
    (fuel : Nat) (validationFuel : options.limits.validation = fuel+1)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (thread : Miri.Concurrency.ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (top : thread.topUserRelevantFrame = some frames.size)
    (relevant : caller.extra.userRelevance > 0)
    (budget : Nat) (budgetEq : limits.callDispatch = budget+1)
    (backend : machine.user.payload.payload.user.backend = .none)
    (source : PreparedContracts.SourceComparator) (cmp : ProjectionMetadataFacts.NullComparator)
    (valid19 : 19 < caller.locals.size) (valid21 : 21 < caller.locals.size) (valid24 : 24 < caller.locals.size)
    (live19 : caller.locals[19].value = .live (.immediate (.scalar sourcePointer)))
    (cache19 : caller.locals[19].layout = some CopyCompilerFacts.sourcePointerLayout)
    (live21 : caller.locals[21].value = .live (.immediate (.scalar destinationPointer)))
    (cache21 : caller.locals[21].layout = some CopyCompilerFacts.destPointerLayout)
    (live24 : caller.locals[24].value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))))
    (cache24 : caller.locals[24].layout = some RootCompilerFacts.usizeLayout) :
    Call.evalCallTerminator (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      () limits.callDispatch CopyEvaluateCall.terminator (Storage.withCurrent frames caller machine) =
      .ok () (Storage.withCurrent (frames.push (cachedCaller caller valid))
        (initialized (Storage.withCurrent frames (cachedCaller caller valid) machine)
          (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 18 CopyHelperUnit.layout).stackView (.goto (some 9) .Continue) noRace sourcePointer destinationPointer n)
        (CallEntryFacts.freshRoot machine).1) := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits
  let state := Storage.withCurrent frames caller machine
  let cachedFrame := cachedCaller caller valid
  let cachedState := Storage.withCurrent frames cachedFrame machine
  let destination := (LocalPlaces.localRuntimePlace frames.size cachedFrame 18 CopyHelperUnit.layout).stackView
  let after := Storage.withCurrent (frames.push cachedFrame)
    (initialized cachedState destination (.goto (some 9) .Continue) noRace sourcePointer destinationPointer n) (CallEntryFacts.freshRoot machine).1
  have valid18' : 18 < cachedFrame.locals.size := by simpa [cachedFrame,cachedCaller,LocalPlaces.cachePlaceLayout] using valid
  have valid19' : 19 < cachedFrame.locals.size := by simpa [cachedFrame,cachedCaller,LocalPlaces.cachePlaceLayout] using valid19
  have valid21' : 21 < cachedFrame.locals.size := by simpa [cachedFrame,cachedCaller,LocalPlaces.cachePlaceLayout] using valid21
  have valid24' : 24 < cachedFrame.locals.size := by simpa [cachedFrame,cachedCaller,LocalPlaces.cachePlaceLayout] using valid24
  have live18' : cachedFrame.locals[18].value = .live (.immediate old) := by
    simpa [cachedFrame,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set] using live
  have cached18' : cachedFrame.locals[18].layout = some CopyHelperUnit.layout := by
    simp [cachedFrame,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set_self]
  have live19' : cachedFrame.locals[19].value = .live (.immediate (.scalar sourcePointer)) := by
    simpa [cachedFrame,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set] using live19
  have cache19' : cachedFrame.locals[19].layout = some CopyCompilerFacts.sourcePointerLayout := by
    simpa [cachedFrame,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set] using cache19
  have live21' : cachedFrame.locals[21].value = .live (.immediate (.scalar destinationPointer)) := by
    simpa [cachedFrame,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set] using live21
  have cache21' : cachedFrame.locals[21].layout = some CopyCompilerFacts.destPointerLayout := by
    simpa [cachedFrame,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set] using cache21
  have live24' : cachedFrame.locals[24].value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))) := by
    simpa [cachedFrame,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set] using live24
  have cache24' : cachedFrame.locals[24].layout = some RootCompilerFacts.usizeLayout := by
    simpa [cachedFrame,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set] using cache24
  have evaluated := CopyEvaluateCall.evaluate options limits (remaining+1) span debug source cmp frames cachedFrame machine sourcePointer destinationPointer n
    body identity callee location valid19' valid21' valid24' live19' cache19' live21' cache21' live24' cache24' noClocks ghost
  have dest := CallUncachedLocal.uncached options limits (remaining+1) span debug frames caller machine 18
    CopyHelperUnit.layout valid uncached CopyHelperUnit.layout_shape.2.1
    (compute_local18 frames caller machine body identity callee)
  have dispatched := CopyDispatchEntry.actual_dispatch options limits remaining span debug frames cachedFrame machine tracker tracked sourcePointer destinationPointer n 18 valid18'
    old live18' cached18' noClocks noRace body identity callee trackNone location fuel validationFuel ghost shallow
    thread active frames.size top cachedFrame (by simp [cachedState,Storage.withCurrent])
    (by simp) relevant budget budgetEq backend (some 9) .Continue budget
  have canUnwind : h.abiCanUnwind HelperCompilerFacts.copyAbi = true := CopyCallFacts.abi_flags.2.1
  have oldIndex : h.frameIndex state = .ok frames.size state := by
    change (do match (←get).stack.frameIndex with
      | .ok index => pure index | .error error => throw (.stack error) : MachineHooks.M MiriMemoryKind Machine.RootUser Nat) state = _
    simp [state,Storage.withCurrent,Stack.frameIndex,Array.isEmpty_push,bind,EStateM.bind,
      get,getThe,MonadStateOf.get,EStateM.get,pure,Pure.pure,EStateM.pure,Except.pure]
  have newIndex : h.frameIndex after = .ok (frames.size+1) after := by
    change (do match (←get).stack.frameIndex with
      | .ok index => pure index | .error error => throw (.stack error) : MachineHooks.M MiriMemoryKind Machine.RootUser Nat) after = _
    simp [after,Storage.withCurrent,Stack.frameIndex,Array.isEmpty_push,bind,EStateM.bind,
      get,getThe,MonadStateOf.get,EStateM.get,pure,Pure.pure,EStateM.pure,Except.pure]
  apply GenericCallStages.call_terminator h () limits.callDispatch CopyEvaluateCall.terminator
    HelperCompilerFacts.copyCall.function #[CopyEvaluateCall.argument0,CopyEvaluateCall.argument1,CopyEvaluateCall.argument2] ⟨18,#[]⟩ 9 .Continue .Normal ⟨28⟩
    state cachedState cachedState after caller frames.size (frames.size+1) destination
    ⟨.Instance HelperCompilerFacts.copyCall.callee,
      #[.Copy (CopyInstall.first sourcePointer),.Copy (CopyInstall.second destinationPointer),.Copy (CopyInstall.third n)],.Rust,some HelperCompilerFacts.copyAbi,true⟩
    source_call (CallEntryLocals.get_frame options limits (remaining+1) span frames caller machine) oldIndex dest evaluated
  · simpa only [budgetEq,Option.any,canUnwind,ite_true] using dispatched
  · exact newIndex
  · omega
end DuplicatePrefix.CopyUncachedCall
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.CopyUncachedCall.compute_local18, ``DuplicatePrefix.CopyUncachedCall.call_uncached] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved uncached add call dependency {dependency}"
