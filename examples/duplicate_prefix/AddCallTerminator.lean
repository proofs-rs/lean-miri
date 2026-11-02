import duplicate_prefix.AddDispatchEntry
import duplicate_prefix.AddEvaluateCall
namespace DuplicatePrefix.AddCallTerminator
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CanonicalConfigFacts AddEntry
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
 theorem source_call : AddEvaluateCall.terminator.kind =
    .Call HelperCompilerFacts.addCall.function #[AddEvaluateCall.argument0,AddEvaluateCall.argument1]
      ⟨21,#[]⟩ (some 8) .Continue .Normal ⟨34⟩ := by with_unfolding_all rfl
 theorem call (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (debug : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (pointer : Scalar Provenance) (n : UInt64) (valid : 21 < caller.locals.size)
    (old : Immediate Provenance) (live : caller.locals[21].value = .live (.immediate old))
    (cached : caller.locals[21].layout = some CopyCompilerFacts.destPointerLayout)
    (noClocks : caller.extra.dataRace = none) (noRace : machine.dataRace = none)
    (body : caller.body = RootBody.reflected.body.body) (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance) (trackNone : caller.trackCallerArg = none)
    (location : caller.location = .mir ⟨7,RootCallerLocation.statementCount 7⟩)
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
    (valid22 : 22 < caller.locals.size) (valid23 : 23 < caller.locals.size)
    (live22 : caller.locals[22].value = .live (.immediate (.scalar pointer)))
    (cache22 : caller.locals[22].layout = some CopyCompilerFacts.destPointerLayout)
    (live23 : caller.locals[23].value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))))
    (cache23 : caller.locals[23].layout = some RootCompilerFacts.usizeLayout) :
    Call.evalCallTerminator (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      () limits.callDispatch AddEvaluateCall.terminator (Storage.withCurrent frames caller machine) =
      .ok () (Storage.withCurrent (frames.push caller)
        (initialized (Storage.withCurrent frames caller machine)
          (LocalPlaces.localRuntimePlace frames.size caller 21 CopyCompilerFacts.destPointerLayout).stackView (.goto (some 8) .Continue) noRace pointer n)
        (CallEntryFacts.freshRoot machine).1) := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits
  let state := Storage.withCurrent frames caller machine
  let dest := (LocalPlaces.localRuntimePlace frames.size caller 21 CopyCompilerFacts.destPointerLayout).stackView
  let after := Storage.withCurrent (frames.push caller)
    (initialized state dest (.goto (some 8) .Continue) noRace pointer n) (CallEntryFacts.freshRoot machine).1
  have statementCount : RootCallerLocation.statementCount 7 = 13 := by with_unfolding_all rfl
  have located : caller.location = .mir ⟨7,13⟩ := by simpa only [statementCount] using location
  have evaluated := AddEvaluateCall.evaluate options limits (remaining+1) span debug source cmp frames caller machine pointer n
    body identity callee located valid22 valid23 live22 cache22 live23 cache23 noClocks ghost
  have destEval := CallEntryLocals.destination_cached options limits (remaining+1) span debug frames caller machine 21
    CopyCompilerFacts.destPointerLayout valid cached RootRawPointerValidity.mut_pointer_sized
  have dispatched := AddDispatchEntry.actual_dispatch options limits remaining span debug frames caller machine tracker tracked pointer n 21 valid
    old live cached noClocks noRace body identity callee trackNone location fuel validationFuel ghost shallow
    thread active index top cachedFrame indexValid lookup relevant budget budgetEq backend (some 8) .Continue budget
  have canUnwind : h.abiCanUnwind HelperCompilerFacts.addAbi = true := AddCallFacts.abi_flags.2.1
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
  apply GenericCallStages.call_terminator h () limits.callDispatch AddEvaluateCall.terminator
    HelperCompilerFacts.addCall.function #[AddEvaluateCall.argument0,AddEvaluateCall.argument1] ⟨21,#[]⟩ 8 .Continue .Normal ⟨34⟩
    state state state after caller frames.size (frames.size+1) dest
    ⟨.Instance HelperCompilerFacts.addCall.callee,
      #[.Copy (AddInstall.first pointer),.Copy (AddInstall.second n)],.Rust,some HelperCompilerFacts.addAbi,true⟩
    source_call (CallEntryLocals.get_frame options limits (remaining+1) span frames caller machine) oldIndex destEval evaluated
  · simpa only [budgetEq,Option.any,canUnwind,ite_true] using dispatched
  · exact newIndex
  · omega
end DuplicatePrefix.AddCallTerminator
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.AddCallTerminator.call) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved add call terminator dependency {dependency}"
