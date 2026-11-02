import duplicate_prefix.AddCallTerminator
import duplicate_prefix.CallUncachedLocal
namespace DuplicatePrefix.AddUncachedCall
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CanonicalConfigFacts AddEntry AddCallTerminator
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable def cachedCaller (caller : CompilerFrameContext.ActualFrame) (valid : 21 < caller.locals.size) :=
  LocalPlaces.cachePlaceLayout caller 21 CopyCompilerFacts.destPointerLayout valid
 theorem compute_local21 (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : caller.body = RootBody.reflected.body.body) (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance) :
    CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler 21 (Storage.withCurrent frames caller machine) =
      .ok CopyCompilerFacts.destPointerLayout (Storage.withCurrent frames caller machine) := by
  have normalized : CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler caller 21 = .ok 8 := by
    unfold CompilerFrameContext.normalizedLocalType CompilerFrameContext.normalizedBody CompilerFrameContext.bodyOfFrame
    rw [body,identity,callee]
    with_unfolding_all rfl
  unfold CompilerFrameContext.computeLocalLayout
  simp only [MachineHooks.currentFrame,Storage.withCurrent,Stack.currentFrame?,Array.back?_push,
    bind,EStateM.bind,get,getThe,MonadStateOf.get,EStateM.get,pure,EStateM.pure]
  rw [normalized]
  with_unfolding_all change (match PreparedReflection.actual.runtime.lookup 8 with
    | .ok value => EStateM.Result.ok value (Storage.withCurrent frames caller machine)
    | .error error => EStateM.Result.error (StepError.unsupported s!"compiler frame query: {toString error}")
        (Storage.withCurrent frames caller machine)) = _
  rw [CopyCompilerFacts.dest_pointer_layout_eq]
  rfl
 theorem call_uncached (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (debug : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (pointer : Scalar Provenance) (n : UInt64) (valid : 21 < caller.locals.size)
    (old : Immediate Provenance) (live : caller.locals[21].value = .live (.immediate old))
    (uncached : caller.locals[21].layout = none)
    (noClocks : caller.extra.dataRace = none) (noRace : machine.dataRace = none)
    (body : caller.body = RootBody.reflected.body.body) (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance) (trackNone : caller.trackCallerArg = none)
    (location : caller.location = .mir ⟨7,RootCallerLocation.statementCount 7⟩)
    (fuel : Nat) (validationFuel : options.limits.validation = fuel+1)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (thread : Miri.Concurrency.ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (top : thread.topUserRelevantFrame = some frames.size)
    (relevant : caller.extra.userRelevance > 0)
    (budget : Nat) (budgetEq : limits.callDispatch = budget+1)
    (backend : machine.user.payload.payload.user.backend = .none)
    (source : PreparedContracts.SourceComparator) (cmp : ProjectionMetadataFacts.NullComparator)
    (valid22 : 22 < caller.locals.size) (valid23 : 23 < caller.locals.size)
    (live22 : caller.locals[22].value = .live (.immediate (.scalar pointer)))
    (cache22 : caller.locals[22].layout = some CopyCompilerFacts.destPointerLayout)
    (live23 : caller.locals[23].value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))))
    (cache23 : caller.locals[23].layout = some RootCompilerFacts.usizeLayout) :
    Call.evalCallTerminator (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      () limits.callDispatch AddEvaluateCall.terminator (Storage.withCurrent frames caller machine) =
      .ok () (Storage.withCurrent (frames.push (cachedCaller caller valid))
        (initialized (Storage.withCurrent frames (cachedCaller caller valid) machine)
          (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 21 CopyCompilerFacts.destPointerLayout).stackView (.goto (some 8) .Continue) noRace pointer n)
        (CallEntryFacts.freshRoot machine).1) := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits
  let state := Storage.withCurrent frames caller machine
  let cachedFrame := cachedCaller caller valid
  let cachedState := Storage.withCurrent frames cachedFrame machine
  let destination := (LocalPlaces.localRuntimePlace frames.size cachedFrame 21 CopyCompilerFacts.destPointerLayout).stackView
  let after := Storage.withCurrent (frames.push cachedFrame)
    (initialized cachedState destination (.goto (some 8) .Continue) noRace pointer n) (CallEntryFacts.freshRoot machine).1
  have valid21' : 21 < cachedFrame.locals.size := by simpa [cachedFrame,cachedCaller,LocalPlaces.cachePlaceLayout] using valid
  have valid22' : 22 < cachedFrame.locals.size := by simpa [cachedFrame,cachedCaller,LocalPlaces.cachePlaceLayout] using valid22
  have valid23' : 23 < cachedFrame.locals.size := by simpa [cachedFrame,cachedCaller,LocalPlaces.cachePlaceLayout] using valid23
  have live21' : cachedFrame.locals[21].value = .live (.immediate old) := by
    simpa [cachedFrame,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set] using live
  have cached21' : cachedFrame.locals[21].layout = some CopyCompilerFacts.destPointerLayout := by
    simp [cachedFrame,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set_self]
  have live22' : cachedFrame.locals[22].value = .live (.immediate (.scalar pointer)) := by
    simpa [cachedFrame,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set] using live22
  have cache22' : cachedFrame.locals[22].layout = some CopyCompilerFacts.destPointerLayout := by
    simpa [cachedFrame,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set] using cache22
  have live23' : cachedFrame.locals[23].value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))) := by
    simpa [cachedFrame,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set] using live23
  have cache23' : cachedFrame.locals[23].layout = some RootCompilerFacts.usizeLayout := by
    simpa [cachedFrame,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set] using cache23
  have evaluated := AddEvaluateCall.evaluate options limits (remaining+1) span debug source cmp frames cachedFrame machine pointer n
    body identity callee location valid22' valid23' live22' cache22' live23' cache23' noClocks ghost
  have dest := CallUncachedLocal.uncached options limits (remaining+1) span debug frames caller machine 21
    CopyCompilerFacts.destPointerLayout valid uncached RootRawPointerValidity.mut_pointer_sized
    (compute_local21 frames caller machine body identity callee)
  have dispatched := AddDispatchEntry.actual_dispatch options limits remaining span debug frames cachedFrame machine tracker tracked pointer n 21 valid21'
    old live21' cached21' noClocks noRace body identity callee trackNone location fuel validationFuel ghost shallow
    thread active frames.size top cachedFrame (by simp [cachedState,Storage.withCurrent])
    (by simp) relevant budget budgetEq backend (some 8) .Continue budget
  have canUnwind : h.abiCanUnwind HelperCompilerFacts.addAbi = true := AddCallFacts.abi_flags.2.1
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
  apply GenericCallStages.call_terminator h () limits.callDispatch AddEvaluateCall.terminator
    HelperCompilerFacts.addCall.function #[AddEvaluateCall.argument0,AddEvaluateCall.argument1] ⟨21,#[]⟩ 8 .Continue .Normal ⟨34⟩
    state cachedState cachedState after caller frames.size (frames.size+1) destination
    ⟨.Instance HelperCompilerFacts.addCall.callee,
      #[.Copy (AddInstall.first pointer),.Copy (AddInstall.second n)],.Rust,some HelperCompilerFacts.addAbi,true⟩
    source_call (CallEntryLocals.get_frame options limits (remaining+1) span frames caller machine) oldIndex dest evaluated
  · simpa only [budgetEq,Option.any,canUnwind,ite_true] using dispatched
  · exact newIndex
  · omega
end DuplicatePrefix.AddUncachedCall
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.AddUncachedCall.compute_local21, ``DuplicatePrefix.AddUncachedCall.call_uncached] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved uncached add call dependency {dependency}"
