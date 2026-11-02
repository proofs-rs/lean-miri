import duplicate_prefix.RuntimeZeroCallStep
import duplicate_prefix.CallUncachedLocal
namespace DuplicatePrefix.RuntimeZeroUncached
open Miri Miri.Input Miri.ABI Miri.MIR Miri.Interpreter Miri.Memory Miri.TreeBorrows
open DuplicatePrefix RuntimeZeroCallStep
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable def cachedCaller (caller : CompilerFrameContext.ActualFrame) (valid : 1 < caller.locals.size) :=
  LocalPlaces.cachePlaceLayout caller 1 RootCompilerFacts.boolLayout valid
theorem compute_local1 (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : caller.body = CopyPreconditions.Bodies.checkLanguage.loaded.body) (identity : caller.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity)
    (callee : caller.functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance) :
    CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler 1 (Storage.withCurrent frames caller machine) =
      .ok RootCompilerFacts.boolLayout (Storage.withCurrent frames caller machine) := by
  have normalized : CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler caller 1 = .ok 0 := by
    unfold CompilerFrameContext.normalizedLocalType CompilerFrameContext.normalizedBody CompilerFrameContext.bodyOfFrame
    rw [body,identity,callee]
    with_unfolding_all rfl
  unfold CompilerFrameContext.computeLocalLayout
  simp only [MachineHooks.currentFrame,Storage.withCurrent,Stack.currentFrame?,Array.back?_push,
    bind,EStateM.bind,get,getThe,MonadStateOf.get,EStateM.get,pure,EStateM.pure]
  rw [normalized]
  with_unfolding_all change (match PreparedReflection.actual.runtime.lookup 0 with
    | .ok value => EStateM.Result.ok value (Storage.withCurrent frames caller machine)
    | .error error => EStateM.Result.error (StepError.unsupported s!"compiler frame query: {toString error}")
        (Storage.withCurrent frames caller machine)) = _
  rw [RootCompilerFacts.bool_layout_eq]
  rfl

theorem call_uncached
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget + 1)
    (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (original : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : original.body = CopyPreconditions.Bodies.checkLanguage.loaded.body)
    (identity : original.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity)
    (callee : original.functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance)
    (location : original.location = .mir ⟨0,3⟩)
    (originalSize : 1 < original.locals.size)
    (originalLive : original.locals[1].value = .live (.immediate .uninit))
    (originalUncached : original.locals[1].layout = none)
    (originalNoClocks : original.extra.dataRace = none)
    (noRace : machine.dataRace = none)
    (backend : machine.user.payload.payload.user.backend = .none)
    (ghost : machine.user.payload.ghost = false)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (thread : Concurrency.ThreadRecord) (threadIndex : Nat)
    (current : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (RuntimeZeroEntryFacts.pushed options.userRelevantCrates
      (Storage.withCurrent frames (cachedCaller original originalSize) machine) (RuntimeZeroEntry.destination frames original)).stack
      thread.topUserRelevantFrame = some threadIndex)
    (present : (RuntimeZeroEntryFacts.pushed options.userRelevantCrates
      (Storage.withCurrent frames (cachedCaller original originalSize) machine) (RuntimeZeroEntry.destination frames original)).stack.frames[threadIndex]? = some current)
 :
    Call.evalCallTerminator
      (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits)
      () limits.callDispatch
      (CopyPreconditions.Bodies.checkLanguage.loaded.body.basicBlocks[0]'(by with_unfolding_all decide +kernel)).terminator
      (Storage.withCurrent frames original machine) =
      .ok () (Storage.withCurrent (frames.push (cachedCaller original originalSize))
        (RuntimeZeroDone.doneFrame (RuntimeZeroEntry.rawFrame options (Storage.withCurrent frames (cachedCaller original originalSize) machine)
          (RuntimeZeroEntry.destination frames original)))
        (RuntimeZeroEntry.pushedMachine options (Storage.withCurrent frames (cachedCaller original originalSize) machine)
          (RuntimeZeroEntry.destination frames original) current)) := by
  let caller := cachedCaller original originalSize
  have callerSize : 1 < caller.locals.size := by simpa [caller,cachedCaller,LocalPlaces.cachePlaceLayout] using originalSize
  have callerLive : caller.locals[1].value = .live (.immediate .uninit) := by simpa [caller,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set_self] using originalLive
  have callerCached : caller.locals[1].layout = some RootCompilerFacts.boolLayout := by simp [caller,cachedCaller,LocalPlaces.cachePlaceLayout]
  have body : caller.body = CopyPreconditions.Bodies.checkLanguage.loaded.body := body
  have identity := identity
  have callee := callee
  have location := location
  have callerNoClocks := originalNoClocks
  let originalState := Storage.withCurrent frames original machine
  let config := PreparedContracts.actualConfig options () (remaining + 1) span
  let h := ExecutionMachine.callHooks config limits
  let state := Storage.withCurrent frames caller machine
  let dest := destination frames caller
  let block := CopyPreconditions.Bodies.checkLanguage.loaded.body.basicBlocks[0]'(by with_unfolding_all decide +kernel)
  let terminator := block.terminator
  have fields := CanonicalConfigFacts.actual_fields options () (remaining + 1) span
  have termKind : terminator.kind =
      .Call function #[] ⟨1,#[]⟩ (some 1) .Continue .Misc ⟨159⟩ := by
    with_unfolding_all rfl
  have blockAt : caller.body.basicBlocks[0]? = some block := by
    rw [body]
    with_unfolding_all rfl
  have noStatement : block.statements[3]? = none := by
    with_unfolding_all rfl
  have functionEval : h.evalOperandAt () (OperandPath.instruction "function") function state =
      .ok ⟨.immediate .uninit,RuntimeCallQueries.functionLayout⟩ state := by
    change OperandMachine.evalOperandAt (ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits))
      () (OperandPath.instruction "function") function none state = _
    rw [function]
    exact RuntimeFunctionConstant.function_operand options limits (remaining+1) span source debugOff
      frames caller machine (congrArg (·.index) identity) location callee
  have signature : h.functionSignature () RuntimeCallQueries.functionLayout =
      pure (0,ABI.ExternAbi.Rust) := by
    change config.calls.compiler.functionSignature () _ = _
    rw [fields.callCompiler]
    simp only [CompilerCallConstruction.compiler,CompilerExecutionCallLeaves.make]
    rw [RuntimeCallQueries.functionLayout_shape.1,RuntimeCallQueries.function_signature_query]
    simp only [bind,Except.bind,pure,Except.pure]
    rw [RuntimeCallQueries.decode_rust_extern_abi cmp]
    with_unfolding_all rfl
  have kind : h.functionKind RuntimeCallQueries.functionLayout.ty =
      pure (.FnDef 24 #[]) := by
    change config.calls.compiler.functionKind _ = _
    rw [fields.callCompiler]
    with_unfolding_all change (match CompilerFunctionFacts.kind PreparedReflection.actual.compiler.functions
      RuntimeCallQueries.functionLayout.ty with
      | .ok value => pure value
      | .error reason => throw (.unsupported reason) :
        MachineHooks.M MiriMemoryKind Machine.RootUser CallFunctionKind) = _
    rw [RuntimeCallQueries.functionLayout_shape.1,RuntimeCallQueries.function_kind]
  have resolve : h.resolve () 24 #[] state = .ok GuardCompilerFacts.runtimeCall.callee state := by
    change config.calls.compiler.resolve () 24 #[] state = _
    rw [fields.callCompiler]
    exact RuntimeCallQueries.resolve_current frames caller machine body identity callee location
  have itemKind : GuardCompilerFacts.runtimeCall.callee.kind = .Item 24 := by
    rw [RuntimeCallQueries.function_kind_matches_call]
  have fnAbi : h.fnAbiOfInstance () GuardCompilerFacts.runtimeCall.callee #[] = pure GuardCompilerFacts.runtimeAbi := by
    funext st
    exact GuardCompilerFacts.actual_runtime_abi options () (remaining+1) span st
  have callerLocation : h.requiresCallerLocation GuardCompilerFacts.runtimeCall.callee = pure false := by
    funext st
    exact GuardCompilerFacts.actual_runtime_caller_location options () (remaining+1) span limits st
  have calleeEval := GenericCallStages.eval_callee_zero h () function ⟨1,#[]⟩
    ⟨.immediate .uninit,RuntimeCallQueries.functionLayout⟩ state state .Rust 24 #[]
    GuardCompilerFacts.runtimeCall.callee 24 GuardCompilerFacts.runtimeAbi false
    functionEval signature kind resolve itemKind fnAbi callerLocation
  have destinationEval := CallUncachedLocal.uncached options limits (remaining+1) span debugOff
    frames original machine 1 RootCompilerFacts.boolLayout originalSize originalUncached (by decide +kernel)
    (compute_local1 frames original machine body identity callee)
  have destEq : dest = RuntimeZeroEntry.destination frames caller := by rfl
  have destinationEval' : h.evalPlace () ⟨1,#[]⟩ false originalState = .ok dest state := by
    exact destinationEval
  let call : EvaluatedCall Provenance Unit ABI.ExternAbi (FnAbi TyId) :=
    ⟨.Instance GuardCompilerFacts.runtimeCall.callee,#[],.Rust,some GuardCompilerFacts.runtimeAbi,false⟩
  have calleeEval' : Call.evalCalleeAndArgs h () function #[] ⟨1,#[]⟩ state = .ok call state := by
    simpa [call,dest,destination] using calleeEval
  let after := Storage.withCurrent (frames.push caller)
    (RuntimeZeroDone.doneFrame (RuntimeZeroEntry.rawFrame options state (RuntimeZeroEntry.destination frames caller)))
    (RuntimeZeroEntry.pushedMachine options state (RuntimeZeroEntry.destination frames caller) current)
  let request : CallRequest Provenance Unit ABI.ExternAbi (FnAbi TyId) :=
    ⟨.Instance GuardCompilerFacts.runtimeCall.callee,.Rust,some GuardCompilerFacts.runtimeAbi,#[],false,
      RuntimeZeroEntry.destination frames caller,some 1,.Continue⟩
  have find := RuntimeZeroDispatch.find_mir options limits (remaining+1) span state #[]
    (RuntimeZeroEntry.destination frames caller) (some 1) .Continue backend noRace
  have canUnwind : h.abiCanUnwind GuardCompilerFacts.runtimeAbi = true := by
    change GuardCompilerFacts.runtimeAbi.canUnwind = true
    exact congrArg (fun x => x.2.2.2.2.2) GuardCompilerFacts.runtime_abi_shape
  have abiEq : GuardCompilerFacts.languageAbi = GuardCompilerFacts.runtimeAbi := by decide +kernel
  have rustCall : h.isRustCall ABI.ExternAbi.Rust = false := by
    change config.calls.compiler.isRustCall .Rust = false
    rw [fields.callCompiler]
    rfl
  have dispatchStep : Call.initFnCallStep h () request state = .ok none after := by
    have item := CallItemDispatch.item_step h GuardCompilerFacts.runtimeCall.callee 24 GuardCompilerFacts.runtimeAbi
      #[] false (RuntimeZeroEntry.destination frames caller) (some 1) .Continue .Rust itemKind canUnwind rustCall
    rw [item]
    simp only [CallItemDispatch.itemStage, bind, EStateM.bind]
    have find' := find
    change h.findMirOrEvalFn () GuardCompilerFacts.runtimeCall.callee GuardCompilerFacts.runtimeAbi #[]
      (RuntimeZeroEntry.destination frames caller) (some 1) .Continue state = _ at find'
    rw [find']
    simp only [bind, EStateM.bind, pure, EStateM.pure]
    have enter := RuntimeZeroEntry.actual_entry options limits remaining span debugOff frames caller machine
      callerSize callerLive callerCached callerNoClocks noRace ghost tracker tracked thread threadIndex current active top present
    have enter' : Call.initStackFrame h () GuardCompilerFacts.runtimeCall.callee
        CopyPreconditions.Bodies.languageRuntime.loaded GuardCompilerFacts.runtimeAbi #[] false
        (RuntimeZeroEntry.destination frames caller) (.goto (some 1) .Continue)
        (Storage.withCurrent frames caller machine) = .ok ()
        (Storage.withCurrent (frames.push caller)
          (RuntimeZeroDone.doneFrame (RuntimeZeroEntry.rawFrame options
            (Storage.withCurrent frames caller machine) (RuntimeZeroEntry.destination frames caller)))
          (RuntimeZeroEntry.pushedMachine options (Storage.withCurrent frames caller machine)
            (RuntimeZeroEntry.destination frames caller) current)) := by
      rw [← abiEq]
      exact enter
    rw [enter']
  have init : Call.initFnCall h () limits.callDispatch request state = .ok () after := by
    have step := CallItemDispatch.dispatch_one h request state after budget dispatchStep
    simpa [dispatchFuel] using step
  have init' : Call.initFnCall h () limits.callDispatch
      ⟨call.callee,call.callerAbi,call.fnAbi,call.args,call.withCallerLocation,
        RuntimeZeroEntry.destination frames caller,some 1,
        if call.fnAbi.any h.abiCanUnwind then .Continue else .Unreachable⟩ state = .ok () after := by
    simpa [request,call,canUnwind,Option.any] using init
  have getFrame : h.getFrame originalState = .ok original originalState := by
    exact CallEntryLocals.get_frame options limits (remaining+1) span frames original machine
  have oldIndex : h.frameIndex originalState = .ok frames.size originalState := by
    change (do match (← get).stack.frameIndex with
      | .ok index => pure index
      | .error error => throw (.stack error) : MachineHooks.M MiriMemoryKind Machine.RootUser Nat) originalState = _
    simp [originalState,Storage.withCurrent,Stack.frameIndex,Array.isEmpty_push,bind,EStateM.bind,
      get,getThe,MonadStateOf.get,EStateM.get,pure,Pure.pure,EStateM.pure,Except.pure]
  have newIndex : h.frameIndex after = .ok (frames.size+1) after := by
    change (do match (← get).stack.frameIndex with
      | .ok index => pure index
      | .error error => throw (.stack error) : MachineHooks.M MiriMemoryKind Machine.RootUser Nat) after = _
    simp [after,Storage.withCurrent,Stack.frameIndex,Array.isEmpty_push,bind,EStateM.bind,
      get,getThe,MonadStateOf.get,EStateM.get,pure,Pure.pure,EStateM.pure,Except.pure]
  have progress : frames.size + 1 ≠ frames.size := by omega
  exact GenericCallStages.call_terminator h () limits.callDispatch block.terminator function #[] ⟨1,#[]⟩
    1 .Continue .Misc ⟨159⟩ originalState state state after original frames.size (frames.size+1)
    (RuntimeZeroEntry.destination frames caller) call termKind getFrame oldIndex
    (by simpa [destEq] using destinationEval') calleeEval' init' newIndex progress


end DuplicatePrefix.RuntimeZeroUncached

open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.RuntimeZeroUncached.compute_local1, ``DuplicatePrefix.RuntimeZeroUncached.call_uncached] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved language cache dependency {dependency}"
