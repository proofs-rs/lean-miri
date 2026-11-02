import duplicate_prefix.LenEvaluateCall
import duplicate_prefix.LenDispatch
import duplicate_prefix.CallItemDispatch
import duplicate_prefix.MetadataCallTerminator
namespace DuplicatePrefix.LenCallFrontend
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
open CanonicalConfigFacts
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem dispatch_of_entry (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining budget : Nat) (span : PreparedContracts.FixedSpanQuery)
    (state after : RootState) (value : Immediate Provenance) (destination : RuntimeStackPlace Provenance)
    (backend : state.machine.user.payload.payload.user.backend = .none) (race : state.machine.dataRace = none)
    (entry : Call.initStackFrame (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits) ()
      LenHelper.resolved.callee LenHelper.body LenHelper.abi #[.Copy ⟨.immediate value,LenHelper.rawLayout⟩]
      false destination (.goto (some 3) .Continue) state = .ok () after) :
    Call.initFnCall (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits) ()
      (budget+1) ⟨.Instance LenHelper.resolved.callee,.Rust,some LenHelper.abi,
      #[.Copy ⟨.immediate value,LenHelper.rawLayout⟩],false,destination,some 3,.Continue⟩ state = .ok () after := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits
  let args : Array (FnArg Provenance) := #[.Copy ⟨.immediate value,LenHelper.rawLayout⟩]
  have find := LenDispatch.find_mir options limits remaining span state args destination (some 3) .Continue backend race
  have rust : h.isRustCall .Rust = false := by
    change (PreparedContracts.actualConfig options () remaining span).calls.compiler.isRustCall .Rust = false
    rw [(CanonicalConfigFacts.actual_fields options () remaining span).callCompiler]
    rfl
  apply CallItemDispatch.dispatch_one h _ state _ budget
  rw [CallItemDispatch.item_step h LenHelper.resolved.callee 1 LenHelper.abi args false destination
    (some 3) .Continue .Rust LenHelper.callee_kind LenCallFacts.abi_flags.2.1 rust]
  unfold CallItemDispatch.itemStage
  simp only [bind,EStateM.bind]
  rw [find]
  simp only [bind,EStateM.bind]
  dsimp only [h,args]
  rw [entry]
  rfl

def sourceKind : MIR.CallSource := match LenCallSource.callTerminator.kind with
  | .Call _ _ _ _ _ source _ => source
  | _ => .Normal
def fnSpan : MIR.SpanRef := match LenCallSource.callTerminator.kind with
  | .Call _ _ _ _ _ _ span => span
  | _ => ⟨0⟩
theorem source_call : LenCallSource.callTerminator.kind = .Call LenHelper.resolved.function
    #[LenEvaluateCall.argument] ⟨11,#[]⟩ (some 3) .Continue sourceKind fnSpan := by with_unfolding_all rfl

theorem call_of_entry (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
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
    (validDest : 11 < caller.locals.size) (cachedDest : caller.locals[11].layout = some RootCompilerFacts.usizeLayout)
    (noClocks : caller.extra.dataRace = none) (race : machine.dataRace = none)
    (backend : machine.user.payload.payload.user.backend = .none) (ghost : machine.user.payload.ghost = false)
    (afterFrame : CompilerFrameContext.ActualFrame) (afterMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (entry : Call.initStackFrame (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits) ()
      LenHelper.resolved.callee LenHelper.body LenHelper.abi #[.Copy ⟨.immediate value,LenHelper.rawLayout⟩]
      false (LocalPlaces.localRuntimePlace frames.size caller 11 RootCompilerFacts.usizeLayout).stackView (.goto (some 3) .Continue)
      (Storage.withCurrent frames caller machine) = .ok () (Storage.withCurrent (frames.push caller) afterFrame afterMachine)) :
    Call.evalCallTerminator (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits)
      () limits.callDispatch LenCallSource.callTerminator (Storage.withCurrent frames caller machine) =
      .ok () (Storage.withCurrent (frames.push caller) afterFrame afterMachine) := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits
  let state := Storage.withCurrent frames caller machine
  let destination := (LocalPlaces.localRuntimePlace frames.size caller 11 RootCompilerFacts.usizeLayout).stackView
  let after := Storage.withCurrent (frames.push caller) afterFrame afterMachine
  have evaluated := LenEvaluateCall.evaluate options limits remaining span debug source cmp frames caller machine value
    body identity callee located validSource valueSource cachedSource noClocks ghost
  have dest := CallEntryLocals.destination_cached options limits remaining span debug frames caller machine 11
    RootCompilerFacts.usizeLayout validDest cachedDest (by decide +kernel)
  have dispatched := dispatch_of_entry options limits remaining budget span state after value destination backend race entry
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
    LenHelper.resolved.function #[LenEvaluateCall.argument] ⟨11,#[]⟩ 3 .Continue sourceKind fnSpan
    state state state after caller frames.size (frames.size+1) destination
    ⟨.Instance LenHelper.resolved.callee,#[.Copy ⟨.immediate value,LenHelper.rawLayout⟩],.Rust,some LenHelper.abi,false⟩
    source_call (CallEntryLocals.get_frame options limits remaining span frames caller machine) oldIndex dest evaluated
  · simpa only [dispatchFuel,Option.any,canUnwind,ite_true] using dispatched
  · exact newIndex
  · omega
end
end DuplicatePrefix.LenCallFrontend
open Lean Elab Command in
run_cmd do
  for name in [``DuplicatePrefix.LenCallFrontend.dispatch_of_entry, ``DuplicatePrefix.LenCallFrontend.call_of_entry] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved len call frontend {dependency}"
