import duplicate_prefix.MetadataDispatchEntry
import duplicate_prefix.MetadataEvaluateCall
namespace DuplicatePrefix.MetadataCallTerminator
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
open CanonicalConfigFacts MetadataEntry
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def sourceKind : MIR.CallSource := match SliceLenFacts.callTerminator.kind with
  | .Call _ _ _ _ _ source _ => source
  | _ => .Normal
def fnSpan : MIR.SpanRef := match SliceLenFacts.callTerminator.kind with
  | .Call _ _ _ _ _ _ span => span
  | _ => ⟨0⟩
theorem source_call : SliceLenFacts.callTerminator.kind = .Call PtrMetadataHelper.resolved.function
    #[MetadataEvaluateCall.argument] ⟨0,#[]⟩ (some 1) .Continue sourceKind fnSpan := by with_unfolding_all rfl
theorem call (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
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
    (cached : caller.locals[0].layout = some RootCompilerFacts.usizeLayout)
    (noClocks : caller.extra.dataRace = none) (noRace : machine.dataRace = none)
    (backend : machine.user.payload.payload.user.backend = .none)
    (fuel : Nat) (validationFuel : options.limits.validation = fuel+1)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat)
    (current : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (MetadataPush.pushed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller 0 RootCompilerFacts.usizeLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (present : (MetadataPush.pushed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller 0 RootCompilerFacts.usizeLayout).stackView).stack.frames[index]? = some current) :
    Call.evalCallTerminator (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      () limits.callDispatch SliceLenFacts.callTerminator
      (Storage.withCurrent frames caller machine) =
      .ok () (Storage.withCurrent (frames.push caller)
        (initialized options (Storage.withCurrent frames caller machine)
          (LocalPlaces.localRuntimePlace frames.size caller 0 RootCompilerFacts.usizeLayout).stackView
          (PtrMetadataComplete.rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len))
        (MetadataPush.completed options.userRelevantCrates (Storage.withCurrent frames caller machine)
          (LocalPlaces.localRuntimePlace frames.size caller 0 RootCompilerFacts.usizeLayout).stackView current).machine) := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits
  let state := Storage.withCurrent frames caller machine
  let destination := (LocalPlaces.localRuntimePlace frames.size caller 0 RootCompilerFacts.usizeLayout).stackView
  let value := PtrMetadataComplete.rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len
  let after := Storage.withCurrent (frames.push caller) (initialized options state destination value)
    (MetadataPush.completed options.userRelevantCrates state destination current).machine
  have evaluated := MetadataEvaluateCall.evaluate options limits (remaining+1) span debug source cmp frames caller machine value
    body identity callee located valid2 value2 cached2 noClocks ghost
  have dest := CallEntryLocals.destination_cached options limits (remaining+1) span debug frames caller machine 0
    RootCompilerFacts.usizeLayout valid cached (by decide +kernel)
  have dispatched := MetadataDispatchEntry.actual_dispatch options limits remaining budget span debug frames caller machine tracker tracked
    carrier len valid old live cached noClocks noRace backend fuel validationFuel ghost shallow thread index current active top present
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
    state state state after caller frames.size (frames.size+1) destination
    ⟨.Instance PtrMetadataHelper.resolved.callee,#[.Copy ⟨.immediate value,PtrMetadataHelper.rawLayout⟩],.Rust,some PtrMetadataHelper.abi,false⟩
    source_call (CallEntryLocals.get_frame options limits (remaining+1) span frames caller machine) oldIndex dest evaluated
  · simpa only [dispatchFuel,Option.any,canUnwind,ite_true] using dispatched
  · exact newIndex
  · omega
end
end DuplicatePrefix.MetadataCallTerminator
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.MetadataCallTerminator.call) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved metadata call terminator dependency {dependency}"
