import duplicate_prefix.CopyDispatchEntry
import duplicate_prefix.CopyEvaluateCall
namespace DuplicatePrefix.CopyCallTerminator
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CanonicalConfigFacts CopyEntry
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
 theorem source_call : CopyEvaluateCall.terminator.kind =
    .Call HelperCompilerFacts.copyCall.function #[CopyEvaluateCall.argument0,CopyEvaluateCall.argument1,CopyEvaluateCall.argument2]
      ⟨18,#[]⟩ (some 9) .Continue .Normal ⟨28⟩ := by with_unfolding_all rfl
 theorem call (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (debug : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (sourcePointer destinationPointer : Scalar Provenance) (n : UInt64) (valid : 18 < caller.locals.size)
    (old : Immediate Provenance) (live : caller.locals[18].value = .live (.immediate old))
    (cached : caller.locals[18].layout = some CopyHelperUnit.layout)
    (noClocks : caller.extra.dataRace = none) (noRace : machine.dataRace = none)
    (body : caller.body = RootBody.reflected.body.body) (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance) (trackNone : caller.trackCallerArg = none)
    (location : caller.location = .mir ⟨8,RootCallerLocation.statementCount 8⟩)
    (fuel : Nat) (validationFuel : options.limits.validation = fuel+1)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (thread : Miri.Concurrency.ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (index : Nat) (top : thread.topUserRelevantFrame = some index)
    (cachedFrame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (indexValid : index < (frames.push caller).size) (lookup : (frames.push caller)[index]? = some cachedFrame)
    (relevant : cachedFrame.extra.userRelevance > 0)
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
      .ok () (Storage.withCurrent (frames.push caller)
        (initialized (Storage.withCurrent frames caller machine)
          (LocalPlaces.localRuntimePlace frames.size caller 18 CopyHelperUnit.layout).stackView (.goto (some 9) .Continue) noRace sourcePointer destinationPointer n)
        (CallEntryFacts.freshRoot machine).1) := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits
  let state := Storage.withCurrent frames caller machine
  let dest := (LocalPlaces.localRuntimePlace frames.size caller 18 CopyHelperUnit.layout).stackView
  let after := Storage.withCurrent (frames.push caller)
    (initialized state dest (.goto (some 9) .Continue) noRace sourcePointer destinationPointer n) (CallEntryFacts.freshRoot machine).1
  have statementCount : RootCallerLocation.statementCount 8 = 4 := by with_unfolding_all rfl
  have located : caller.location = .mir ⟨8,4⟩ := by simpa only [statementCount] using location
  have evaluated := CopyEvaluateCall.evaluate options limits (remaining+1) span debug source cmp frames caller machine sourcePointer destinationPointer n
    body identity callee located valid19 valid21 valid24 live19 cache19 live21 cache21 live24 cache24 noClocks ghost
  have destEval := CallEntryLocals.destination_cached options limits (remaining+1) span debug frames caller machine 18
    CopyHelperUnit.layout valid cached CopyHelperUnit.layout_shape.2.1
  have dispatched := CopyDispatchEntry.actual_dispatch options limits remaining span debug frames caller machine tracker tracked sourcePointer destinationPointer n 18 valid
    old live cached noClocks noRace body identity callee trackNone location fuel validationFuel ghost shallow
    thread active index top cachedFrame indexValid lookup relevant budget budgetEq backend (some 9) .Continue budget
  have canUnwind : h.abiCanUnwind HelperCompilerFacts.copyAbi = true := CopyCallFacts.abi_flags.2.1
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
  apply GenericCallStages.call_terminator h () limits.callDispatch CopyEvaluateCall.terminator
    HelperCompilerFacts.copyCall.function #[CopyEvaluateCall.argument0,CopyEvaluateCall.argument1,CopyEvaluateCall.argument2] ⟨18,#[]⟩ 9 .Continue .Normal ⟨28⟩
    state state state after caller frames.size (frames.size+1) dest
    ⟨.Instance HelperCompilerFacts.copyCall.callee,
      #[.Copy (CopyInstall.first sourcePointer),.Copy (CopyInstall.second destinationPointer),.Copy (CopyInstall.third n)],.Rust,some HelperCompilerFacts.copyAbi,true⟩
    source_call (CallEntryLocals.get_frame options limits (remaining+1) span frames caller machine) oldIndex destEval evaluated
  · simpa only [budgetEq,Option.any,canUnwind,ite_true] using dispatched
  · exact newIndex
  · omega
end DuplicatePrefix.CopyCallTerminator
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.CopyCallTerminator.call) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved add call terminator dependency {dependency}"
