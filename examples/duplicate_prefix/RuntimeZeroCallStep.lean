import duplicate_prefix.RuntimeZeroReturn
import duplicate_prefix.RuntimeFunctionConstant
import duplicate_prefix.CallEntryLocals
import duplicate_prefix.GenericCallStages
import duplicate_prefix.CallItemDispatch
import duplicate_prefix.RuntimeZeroDispatch
import duplicate_prefix.CopyRuntimeCallFacts

/-! The actual checkLanguage MIR call terminator which enters the zero-argument
    language-runtime helper.  Operand resolution, destination evaluation,
    dispatch and `initStackFrame` are all the production hooks. -/
namespace DuplicatePrefix.RuntimeZeroCallStep
open Miri Miri.Input Miri.ABI Miri.MIR Miri.Interpreter Miri.Memory Miri.TreeBorrows
open DuplicatePrefix
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def function : Operand := .Constant RuntimeFunctionConstant.constant
def destination (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra) :=
  (LocalPlaces.localRuntimePlace frames.size caller 1 RootCompilerFacts.boolLayout).stackView
theorem call_terminator
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget + 1)
    (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : caller.body = CopyPreconditions.Bodies.checkLanguage.loaded.body)
    (identity : caller.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity)
    (callee : caller.functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance)
    (location : caller.location = .mir ⟨0,3⟩)
    (callerSize : 1 < caller.locals.size)
    (callerLive : caller.locals[1].value = .live (.immediate .uninit))
    (callerCached : caller.locals[1].layout = some RootCompilerFacts.boolLayout)
    (callerNoClocks : caller.extra.dataRace = none)
    (noRace : machine.dataRace = none)
    (backend : machine.user.payload.payload.user.backend = .none)
    (ghost : machine.user.payload.ghost = false)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (thread : Concurrency.ThreadRecord) (threadIndex : Nat)
    (current : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (RuntimeZeroEntryFacts.pushed options.userRelevantCrates
      (Storage.withCurrent frames caller machine) (RuntimeZeroEntry.destination frames caller)).stack
      thread.topUserRelevantFrame = some threadIndex)
    (present : (RuntimeZeroEntryFacts.pushed options.userRelevantCrates
      (Storage.withCurrent frames caller machine) (RuntimeZeroEntry.destination frames caller)).stack.frames[threadIndex]? = some current)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    Call.evalCallTerminator
      (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits)
      () limits.callDispatch
      (CopyPreconditions.Bodies.checkLanguage.loaded.body.basicBlocks[0]'(by with_unfolding_all decide +kernel)).terminator
      (Storage.withCurrent frames caller machine) =
      .ok () (Storage.withCurrent (frames.push caller)
        (RuntimeZeroReturn.entryFrame options (Storage.withCurrent frames caller machine)
          (RuntimeZeroEntry.destination frames caller))
        (RuntimeZeroReturn.entryMachine options (Storage.withCurrent frames caller machine)
          (RuntimeZeroEntry.destination frames caller) current)) := by
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
  have destinationEval := CallEntryLocals.destination_cached options limits (remaining+1) span debugOff
    frames caller machine 1 RootCompilerFacts.boolLayout callerSize callerCached (by decide +kernel)
  have destEq : dest = RuntimeZeroEntry.destination frames caller := by rfl
  have destinationEval' : h.evalPlace () ⟨1,#[]⟩ false state = .ok dest state := by
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
  have getFrame : h.getFrame state = .ok caller state := by
    exact CallEntryLocals.get_frame options limits (remaining+1) span frames caller machine
  have oldIndex : h.frameIndex state = .ok frames.size state := by
    change (do match (← get).stack.frameIndex with
      | .ok index => pure index
      | .error error => throw (.stack error) : MachineHooks.M MiriMemoryKind Machine.RootUser Nat) state = _
    simp [state,Storage.withCurrent,Stack.frameIndex,Array.isEmpty_push,bind,EStateM.bind,
      get,getThe,MonadStateOf.get,EStateM.get,pure,Pure.pure,EStateM.pure,Except.pure]
  have newIndex : h.frameIndex after = .ok (frames.size+1) after := by
    change (do match (← get).stack.frameIndex with
      | .ok index => pure index
      | .error error => throw (.stack error) : MachineHooks.M MiriMemoryKind Machine.RootUser Nat) after = _
    simp [after,Storage.withCurrent,Stack.frameIndex,Array.isEmpty_push,bind,EStateM.bind,
      get,getThe,MonadStateOf.get,EStateM.get,pure,Pure.pure,EStateM.pure,Except.pure]
  have progress : frames.size + 1 ≠ frames.size := by omega
  exact GenericCallStages.call_terminator h () limits.callDispatch block.terminator function #[] ⟨1,#[]⟩
    1 .Continue .Misc ⟨159⟩ state state state after caller frames.size (frames.size+1)
    (RuntimeZeroEntry.destination frames caller) call termKind getFrame oldIndex
    (by simpa [destEq] using destinationEval') calleeEval' init' newIndex progress

theorem call_then_runtime_returns_false
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining budget fuel : Nat) (dispatchFuel : limits.callDispatch = budget + 1)
    (validationFuel : options.limits.validation = fuel + 1)
    (span : PreparedContracts.FixedSpanQuery) (source : PreparedContracts.SourceComparator)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : caller.body = CopyPreconditions.Bodies.checkLanguage.loaded.body)
    (identity : caller.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity)
    (callee : caller.functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance)
    (location : caller.location = .mir ⟨0,3⟩)
    (callerSize : 1 < caller.locals.size)
    (callerLive : caller.locals[1].value = .live (.immediate .uninit))
    (callerCached : caller.locals[1].layout = some RootCompilerFacts.boolLayout)
    (callerNoClocks : caller.extra.dataRace = none)
    (noRace : machine.dataRace = none)
    (backend : machine.user.payload.payload.user.backend = .none)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (thread : Concurrency.ThreadRecord) (threadIndex : Nat)
    (current : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (RuntimeZeroEntryFacts.pushed options.userRelevantCrates
      (Storage.withCurrent frames caller machine) (RuntimeZeroEntry.destination frames caller)).stack
      thread.topUserRelevantFrame = some threadIndex)
    (present : (RuntimeZeroEntryFacts.pushed options.userRelevantCrates
      (Storage.withCurrent frames caller machine) (RuntimeZeroEntry.destination frames caller)).stack.frames[threadIndex]? = some current)
    (threadAfter : Concurrency.ThreadRecord)
    (threadAfterEq : threadAfter = PushThread.after thread (frames.push caller).size
      (RuntimeZeroEntryFacts.rank options.userRelevantCrates) current.extra.userRelevance)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    Call.evalCallTerminator
      (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits)
      () limits.callDispatch
      (CopyPreconditions.Bodies.checkLanguage.loaded.body.basicBlocks[0]'(by with_unfolding_all decide +kernel)).terminator
      (Storage.withCurrent frames caller machine) =
      .ok () (Storage.withCurrent (frames.push caller)
        (RuntimeZeroReturn.entryFrame options (Storage.withCurrent frames caller machine)
          (RuntimeZeroEntry.destination frames caller))
        (RuntimeZeroReturn.entryMachine options (Storage.withCurrent frames caller machine)
          (RuntimeZeroEntry.destination frames caller) current)) ∧
    ∃ afterAssign afterReturn,
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining + 1) span) limits ()
        (Storage.withCurrent (frames.push caller)
          (RuntimeZeroReturn.entryFrame options (Storage.withCurrent frames caller machine)
            (RuntimeZeroEntry.destination frames caller))
          (RuntimeZeroReturn.entryMachine options (Storage.withCurrent frames caller machine)
            (RuntimeZeroEntry.destination frames caller) current)) = (afterAssign, .ok true) ∧
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining + 1) span) limits ()
        afterAssign = (afterReturn, .ok true) ∧
      afterReturn = RuntimeZeroReturn.returnedState frames caller (by omega)
        (CopyRuntimeGuardStep.runtimeAfterAssign
          (RuntimeZeroReturn.entryFrame options (Storage.withCurrent frames caller machine)
            (RuntimeZeroEntry.destination frames caller))
          (RuntimeZeroReturn.entry_local0_valid options (Storage.withCurrent frames caller machine)
            (RuntimeZeroEntry.destination frames caller)))
        ((SourceControl.accounted (PreparedContracts.actualConfig options () (remaining + 1) span).terminators
          (Storage.withCurrent (frames.push caller)
            (CopyRuntimeGuardStep.runtimeAfterAssign
              (RuntimeZeroReturn.entryFrame options (Storage.withCurrent frames caller machine)
                (RuntimeZeroEntry.destination frames caller))
              (RuntimeZeroReturn.entry_local0_valid options (Storage.withCurrent frames caller machine)
                (RuntimeZeroEntry.destination frames caller)))
            (RuntimeZeroReturn.entryMachine options (Storage.withCurrent frames caller machine)
              (RuntimeZeroEntry.destination frames caller) current))).machine)
        (threadAfter.topUserRelevantFrame.getD (frames.push caller).size) ∧
      afterReturn.machine.user.payload.ghost = false ∧
      ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl
        afterReturn.machine.user).checkedArithmetic = false ∧
      ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl
        afterReturn.machine.user).gcInterval = 0 ∧
      afterReturn.machine.threads.fixedScheduling = true ∧
      afterReturn.machine.borrowTracker = some tracker ∧
      afterReturn.machine.dataRace = none ∧
      afterReturn.machine.user.payload.validation = .Shallow ∧
      ∃ activeThread, afterReturn.machine.threads.activeThread? = some activeThread := by
  have call := call_terminator options limits remaining budget dispatchFuel span source cmp debugOff
    frames caller machine body identity callee location callerSize callerLive callerCached callerNoClocks
    noRace backend ghost tracker tracked thread threadIndex current active top present unchecked noGc fixed
  have execution := RuntimeZeroReturn.actual_entry_then_body_returns_false options limits remaining span
    source debugOff fuel validationFuel frames caller machine callerSize callerLive callerCached callerNoClocks
    noRace ghost shallow tracker tracked thread threadIndex current active top present threadAfter threadAfterEq
    unchecked noGc fixed
  rcases execution with ⟨_, afterAssign, afterReturn, stepAssign, stepReturn, returnState,
    returnGhost, returnUnchecked, returnNoGc, returnFixed, returnTracked, returnNoRace, returnShallow,
    returnActive⟩
  exact ⟨call, afterAssign, afterReturn, stepAssign, stepReturn, by simpa using returnState,
    returnGhost, returnUnchecked, returnNoGc, returnFixed, returnTracked, returnNoRace, returnShallow,
    returnActive⟩

theorem call_runtime_then_parent_false_branch
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining budget fuel : Nat) (dispatchFuel : limits.callDispatch = budget + 1)
    (validationFuel : options.limits.validation = fuel + 1)
    (span : PreparedContracts.FixedSpanQuery) (source : PreparedContracts.SourceComparator)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : caller.body = CopyPreconditions.Bodies.checkLanguage.loaded.body)
    (identity : caller.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity)
    (callee : caller.functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance)
    (location : caller.location = .mir ⟨0,3⟩)
    (callerSize : 2 < caller.locals.size)
    (callerLocalsSize : caller.locals.size = 3)
    (callerValid0 : (0 : MIR.LocalId) < caller.locals.size)
    (callerLive0 : caller.locals[0].value = .live (.immediate .uninit))
    (callerUncached0 : caller.locals[0].layout = none)
    (callerOneValid : 1 < caller.locals.size)
    (callerLive1 : caller.locals[1].value = .live (.immediate .uninit))
    (callerCached1 : caller.locals[1].layout = some RootCompilerFacts.boolLayout)
    (callerLive2 : caller.locals[2].value = .live (.immediate .uninit))
    (layout2 : Option LocalLayout)
    (callerLayout2 : caller.locals[2].layout = layout2)
    (callerNoClocks : caller.extra.dataRace = none)
    (noRace : machine.dataRace = none)
    (backend : machine.user.payload.payload.user.backend = .none)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (thread : Concurrency.ThreadRecord) (threadIndex : Nat)
    (current : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (RuntimeZeroEntryFacts.pushed options.userRelevantCrates
      (Storage.withCurrent frames caller machine) (RuntimeZeroEntry.destination frames caller)).stack
      thread.topUserRelevantFrame = some threadIndex)
    (present : (RuntimeZeroEntryFacts.pushed options.userRelevantCrates
      (Storage.withCurrent frames caller machine) (RuntimeZeroEntry.destination frames caller)).stack.frames[threadIndex]? = some current)
    (threadAfter : Concurrency.ThreadRecord)
    (threadAfterEq : threadAfter = PushThread.after thread (frames.push caller).size
      (RuntimeZeroEntryFacts.rank options.userRelevantCrates) current.extra.userRelevance)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    Call.evalCallTerminator
      (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits)
      () limits.callDispatch
      (CopyPreconditions.Bodies.checkLanguage.loaded.body.basicBlocks[0]'(by with_unfolding_all decide +kernel)).terminator
      (Storage.withCurrent frames caller machine) =
      .ok () (Storage.withCurrent (frames.push caller)
        (RuntimeZeroReturn.entryFrame options (Storage.withCurrent frames caller machine)
          (RuntimeZeroEntry.destination frames caller))
        (RuntimeZeroReturn.entryMachine options (Storage.withCurrent frames caller machine)
          (RuntimeZeroEntry.destination frames caller) current)) ∧
    ∃ afterAssign afterReturn deadState branchState,
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining + 1) span) limits ()
        (Storage.withCurrent (frames.push caller)
          (RuntimeZeroReturn.entryFrame options (Storage.withCurrent frames caller machine)
            (RuntimeZeroEntry.destination frames caller))
          (RuntimeZeroReturn.entryMachine options (Storage.withCurrent frames caller machine)
            (RuntimeZeroEntry.destination frames caller) current)) = (afterAssign, .ok true) ∧
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining + 1) span) limits ()
        afterAssign = (afterReturn, .ok true) ∧
      afterReturn = RuntimeZeroReturn.returnedState frames caller callerOneValid
        (CopyRuntimeGuardStep.runtimeAfterAssign
          (RuntimeZeroReturn.entryFrame options (Storage.withCurrent frames caller machine)
            (RuntimeZeroEntry.destination frames caller))
          (RuntimeZeroReturn.entry_local0_valid options (Storage.withCurrent frames caller machine)
            (RuntimeZeroEntry.destination frames caller)))
        ((SourceControl.accounted (PreparedContracts.actualConfig options () (remaining + 1) span).terminators
          (Storage.withCurrent (frames.push caller)
            (CopyRuntimeGuardStep.runtimeAfterAssign
              (RuntimeZeroReturn.entryFrame options (Storage.withCurrent frames caller machine)
                (RuntimeZeroEntry.destination frames caller))
              (RuntimeZeroReturn.entry_local0_valid options (Storage.withCurrent frames caller machine)
                (RuntimeZeroEntry.destination frames caller)))
            (RuntimeZeroReturn.entryMachine options (Storage.withCurrent frames caller machine)
              (RuntimeZeroEntry.destination frames caller) current))).machine)
        (threadAfter.topUserRelevantFrame.getD (frames.push caller).size) ∧
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining + 1) span) limits () afterReturn =
        (deadState, .ok true) ∧
      deadState.stack.currentFrame?.map (·.location) = some (.mir ⟨1,1⟩) ∧
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining + 1) span) limits () deadState =
        (branchState, .ok true) ∧
      branchState.stack.currentFrame?.map (·.location) = some (.mir ⟨3,0⟩) ∧
      ∃ branchFrame branchMachine,
        branchState = Storage.withCurrent frames branchFrame branchMachine ∧
        branchFrame.body = CopyPreconditions.Bodies.checkLanguage.loaded.body ∧
        branchFrame.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity ∧
        branchFrame.functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance ∧
        branchFrame.location = .mir ⟨3,0⟩ ∧
        branchFrame.locals.size = 3 ∧
        branchFrame.locals[0]?.map (·.value) = some (.live (.immediate .uninit)) ∧
        branchFrame.locals[0]?.map (·.layout) = some none ∧
        branchFrame.locals[1]?.map (·.value) = some (.live (.immediate (.scalar (.fromBool false)))) ∧
        branchFrame.locals[1]?.map (·.layout) = some (some RootCompilerFacts.boolLayout) ∧
        branchFrame.locals[2]?.map (·.value) = some .dead ∧
        branchFrame.locals[2]?.map (·.layout) = some layout2 ∧
        branchFrame.extra.dataRace = none ∧
        branchMachine.borrowTracker = some tracker ∧ branchMachine.dataRace = none ∧
        tracker.retagMode = .Default ∧ branchMachine.user.payload.ghost = false ∧
        branchMachine.user.payload.validation = .Shallow ∧
        ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
          branchMachine.user).checkedArithmetic = false ∧
        ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
          branchMachine.user).gcInterval = 0 ∧ branchMachine.threads.fixedScheduling = true ∧
        branchFrame.extra.borrowTracker = caller.extra.borrowTracker ∧
        branchFrame.returnPlace = caller.returnPlace ∧
        branchFrame.returnContinuation = caller.returnContinuation ∧
        branchFrame.vaList = caller.vaList ∧
        branchMachine.memory = machine.memory ∧
        branchMachine.user.addresses = machine.user.addresses ∧
        branchMachine.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
        branchMachine.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
        branchMachine.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
        ∃ activeThread, branchMachine.threads.activeThread? = some activeThread := by
  let returnedFrame := CopyRuntimeGuardStep.returnedCallerFrame caller callerOneValid 1
  let helperFrame := RuntimeZeroReturn.entryFrame options (Storage.withCurrent frames caller machine)
    (RuntimeZeroEntry.destination frames caller)
  let helperValid := RuntimeZeroReturn.entry_local0_valid options
    (Storage.withCurrent frames caller machine) (RuntimeZeroEntry.destination frames caller)
  let helperAfter := CopyRuntimeGuardStep.runtimeAfterAssign helperFrame helperValid
  let helperMachine := RuntimeZeroReturn.entryMachine options (Storage.withCurrent frames caller machine)
    (RuntimeZeroEntry.destination frames caller) current
  let accounted := SourceControl.accounted (PreparedContracts.actualConfig options () (remaining + 1) span).terminators
    (Storage.withCurrent (frames.push caller) helperAfter helperMachine)
  let returnedMachine := CopyRuntimeGuardStep.returnedRuntimeMachine frames caller helperAfter accounted.machine
    (threadAfter.topUserRelevantFrame.getD (frames.push caller).size)
  have frameBody : returnedFrame.body = CopyPreconditions.Bodies.checkLanguage.loaded.body := by
    simpa [returnedFrame,CopyRuntimeGuardStep.returnedCallerFrame] using body
  have frameIdentity : returnedFrame.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity := by
    simpa [returnedFrame,CopyRuntimeGuardStep.returnedCallerFrame] using identity
  have frameCallee : returnedFrame.functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance := by
    simpa [returnedFrame,CopyRuntimeGuardStep.returnedCallerFrame] using callee
  have frameLocation : returnedFrame.location = .mir ⟨1,0⟩ := by
    simp [returnedFrame,CopyRuntimeGuardStep.returnedCallerFrame]
  have frameValid1 : 1 < returnedFrame.locals.size := by
    simpa [returnedFrame,CopyRuntimeGuardStep.returnedCallerFrame,Array.size_set] using callerOneValid
  have frameValid2 : 2 < returnedFrame.locals.size := by
    simpa [returnedFrame,CopyRuntimeGuardStep.returnedCallerFrame,Array.size_set] using callerSize
  have frameLive1 : returnedFrame.locals[1].value = .live (.immediate (.scalar (.fromBool false))) := by
    simp [returnedFrame,CopyRuntimeGuardStep.returnedCallerFrame,Array.getElem_set,frameValid1]
  have frameCached1 : returnedFrame.locals[1].layout = some RootCompilerFacts.boolLayout := by
    simp [returnedFrame,CopyRuntimeGuardStep.returnedCallerFrame,Array.getElem_set,frameValid1,callerCached1]
  have frameLive2 : returnedFrame.locals[2].value = .live (.immediate .uninit) := by
    simp [returnedFrame,CopyRuntimeGuardStep.returnedCallerFrame,Array.getElem_set,callerLive2]
  have frameNoClocks : returnedFrame.extra.dataRace = none := by
    simpa [returnedFrame,CopyRuntimeGuardStep.returnedCallerFrame] using callerNoClocks
  have run := call_then_runtime_returns_false options limits remaining budget fuel dispatchFuel validationFuel
    span source cmp debugOff frames caller machine body identity callee location callerOneValid callerLive1
    callerCached1 callerNoClocks noRace backend ghost shallow tracker tracked thread threadIndex current active
    top present threadAfter threadAfterEq unchecked noGc fixed
  rcases run with ⟨call, afterAssign, afterReturn, stepAssign, stepReturn, returnedEq,
    returnGhost, returnUnchecked, returnNoGc, returnFixed, returnTracked, returnNoRace, returnShallow,
    returnActive⟩
  have returnedEq' : afterReturn = Storage.withCurrent frames returnedFrame returnedMachine := by
    simpa [RuntimeZeroReturn.returnedState,returnedFrame,helperFrame,helperValid,helperAfter,helperMachine,
      accounted,returnedMachine,CopyRuntimeGuardStep.returnedCallerFrame] using returnedEq
  have parentGhost : returnedMachine.user.payload.ghost = false := by
    simpa [returnedEq',Storage.withCurrent] using returnGhost
  have parentUnchecked : ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl
      returnedMachine.user).checkedArithmetic = false := by
    simpa [returnedEq',Storage.withCurrent] using returnUnchecked
  have parentNoGc : ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl
      returnedMachine.user).gcInterval = 0 := by
    simpa [returnedEq',Storage.withCurrent] using returnNoGc
  have parentFixed : returnedMachine.threads.fixedScheduling = true := by
    simpa [returnedEq',Storage.withCurrent] using returnFixed
  have parentTracked : returnedMachine.borrowTracker = some tracker := by
    simpa [returnedEq',Storage.withCurrent] using returnTracked
  have parentNoRace : returnedMachine.dataRace = none := by
    simpa [returnedEq',Storage.withCurrent] using returnNoRace
  have parentShallow : returnedMachine.user.payload.validation = .Shallow := by
    simpa [returnedEq',Storage.withCurrent] using returnShallow
  have parentActive : ∃ activeThread, returnedMachine.threads.activeThread? = some activeThread := by
    simpa [returnedEq',Storage.withCurrent] using returnActive
  have dispatch := CopyRuntimeGuardStep.actual_parent_false_dispatch options limits remaining span debugOff frames returnedFrame
      returnedMachine frameBody frameIdentity frameCallee frameLocation frameValid1 frameLive1 frameCached1
      frameValid2 frameLive2 frameNoClocks parentGhost parentUnchecked parentNoGc parentFixed
  rcases dispatch with ⟨deadState, hdead⟩
  rcases hdead with ⟨branchState, hbranch⟩
  have stepDead := hbranch.1
  have deadLocation := hbranch.2.1
  have stepBranch := hbranch.2.2.1
  have branchLocation := hbranch.2.2.2.1
  have branchStateEq := hbranch.2.2.2.2
  let branchFrame := {SourceSteps.deadFrame returnedFrame ⟨1,0⟩ 2 frameValid2 with location := .mir ⟨3,0⟩}
  let branchMachine := (SourceControl.accounted (PreparedContracts.actualConfig options () (remaining+1) span).terminators
    (Storage.withCurrent frames (SourceSteps.deadFrame returnedFrame ⟨1,0⟩ 2 frameValid2) returnedMachine)).machine
  have branchFrameBody : branchFrame.body = CopyPreconditions.Bodies.checkLanguage.loaded.body := by
    simpa [branchFrame,SourceSteps.deadFrame,returnedFrame,CopyRuntimeGuardStep.returnedCallerFrame] using frameBody
  have branchFrameIdentity : branchFrame.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity := by
    simpa [branchFrame,SourceSteps.deadFrame,returnedFrame,CopyRuntimeGuardStep.returnedCallerFrame] using frameIdentity
  have branchFrameCallee : branchFrame.functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance := by
    simpa [branchFrame,SourceSteps.deadFrame,returnedFrame,CopyRuntimeGuardStep.returnedCallerFrame] using frameCallee
  have branchFrameLocation : branchFrame.location = .mir ⟨3,0⟩ := by simp [branchFrame,SourceSteps.deadFrame]
  have branchFrameSize : branchFrame.locals.size = 3 := by
    simpa [branchFrame,SourceSteps.deadFrame,Array.size_set,returnedFrame,
      CopyRuntimeGuardStep.returnedCallerFrame] using callerLocalsSize
  have branchFrameSlot0 : branchFrame.locals[0]?.map (·.value) = some (.live (.immediate .uninit)) ∧
      branchFrame.locals[0]?.map (·.layout) = some none := by
    have v : (0 : MIR.LocalId) < branchFrame.locals.size := by rw [branchFrameSize]; decide
    rw [Array.getElem?_eq_getElem v]
    simp [branchFrame,SourceSteps.deadFrame,returnedFrame,
      CopyRuntimeGuardStep.returnedCallerFrame,callerLive0,callerUncached0,Array.getElem_set]
  have branchFrameSlot1 : branchFrame.locals[1]?.map (·.value) = some
      (.live (.immediate (.scalar (.fromBool false)))) ∧
      branchFrame.locals[1]?.map (·.layout) = some (some RootCompilerFacts.boolLayout) := by
    have v : (1 : MIR.LocalId) < branchFrame.locals.size := by rw [branchFrameSize]; decide
    rw [Array.getElem?_eq_getElem v]
    simp [branchFrame,SourceSteps.deadFrame,returnedFrame,
      CopyRuntimeGuardStep.returnedCallerFrame,callerCached1,Array.getElem_set]
  have branchFrameSlot2 : branchFrame.locals[2]?.map (·.value) = some .dead ∧
      branchFrame.locals[2]?.map (·.layout) = some layout2 := by
    have v : (2 : MIR.LocalId) < branchFrame.locals.size := by rw [branchFrameSize]; decide
    rw [Array.getElem?_eq_getElem v]
    constructor
    · simp [branchFrame,SourceSteps.deadFrame,returnedFrame,
        CopyRuntimeGuardStep.returnedCallerFrame,Array.getElem_set]
    · simp [branchFrame,SourceSteps.deadFrame,returnedFrame,
        CopyRuntimeGuardStep.returnedCallerFrame,Array.getElem_set,callerLayout2,
        show (2 : Nat) ≠ 1 by decide]
  have branchFrameNoClocks : branchFrame.extra.dataRace = none := by
    simpa [branchFrame,SourceSteps.deadFrame,returnedFrame,
      CopyRuntimeGuardStep.returnedCallerFrame] using frameNoClocks
  have branchMachineTracked : branchMachine.borrowTracker = some tracker := by
    simp [branchMachine,SourceControl.accounted,Storage.withCurrent,parentTracked]
  have branchMachineNoRace : branchMachine.dataRace = none := by
    simp [branchMachine,SourceControl.accounted,Storage.withCurrent,parentNoRace]
  have fields := CanonicalConfigFacts.actual_fields options () (remaining+1) span
  have getSet : ∀ control user,
      (PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
        ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.setControl control user) = control := by
    rw [fields.terminators]
    intro control user
    rfl
  let nextControl := TerminatorClock.advance
    ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl returnedMachine.user)
  let nextUser := (PreparedContracts.actualConfig options () (remaining+1) span).terminators.setControl
    nextControl returnedMachine.user
  have branchMachineEq : branchMachine = {returnedMachine with user := nextUser} := by
    simp [branchMachine,SourceControl.accounted,Storage.withCurrent,nextUser,nextControl,fields.terminators]
  have branchControl : (PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      branchMachine.user = nextControl := by
    rw [branchMachineEq]
    change (PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl nextUser = nextControl
    exact getSet nextControl returnedMachine.user
  have payloadGhostKeep : nextUser.payload.ghost = returnedMachine.user.payload.ghost := by
    dsimp [nextUser]
    rw [fields.terminators]
    rfl
  have payloadShallowKeep : nextUser.payload.validation = returnedMachine.user.payload.validation := by
    dsimp [nextUser]
    rw [fields.terminators]
    rfl
  have branchMachineGhost : branchMachine.user.payload.ghost = false := by
    rw [branchMachineEq,payloadGhostKeep]
    exact parentGhost
  have branchMachineShallow : branchMachine.user.payload.validation = .Shallow := by
    rw [branchMachineEq,payloadShallowKeep]
    exact parentShallow
  have branchMachineUnchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      branchMachine.user).checkedArithmetic = false := by
    rw [branchControl]
    simpa [nextControl,TerminatorClock.advance] using parentUnchecked
  have branchMachineNoGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      branchMachine.user).gcInterval = 0 := by
    rw [branchControl]
    simpa [nextControl,TerminatorClock.advance] using parentNoGc
  have branchMachineFixed : branchMachine.threads.fixedScheduling = true := by
    rw [branchMachineEq]
    exact parentFixed
  have branchFrameBorrow : branchFrame.extra.borrowTracker = caller.extra.borrowTracker := by
    simp [branchFrame,SourceSteps.deadFrame,returnedFrame,CopyRuntimeGuardStep.returnedCallerFrame]
  have branchReturnPlace : branchFrame.returnPlace = caller.returnPlace := by
    simp only [branchFrame,SourceSteps.deadFrame,returnedFrame,CopyRuntimeGuardStep.returnedCallerFrame]
  have branchContinuation : branchFrame.returnContinuation = caller.returnContinuation := by
    simp only [branchFrame,SourceSteps.deadFrame,returnedFrame,CopyRuntimeGuardStep.returnedCallerFrame]
  have branchVarargs : branchFrame.vaList = caller.vaList := by
    simp only [branchFrame,SourceSteps.deadFrame,returnedFrame,CopyRuntimeGuardStep.returnedCallerFrame]
  have returnedKeep : returnedMachine.memory = machine.memory ∧
      returnedMachine.user.addresses = machine.user.addresses ∧
      returnedMachine.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
      returnedMachine.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
      returnedMachine.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras := by
    dsimp only [returnedMachine,CopyRuntimeGuardStep.returnedRuntimeMachine]
    unfold GenericPopFrame.afterRelevanceAt
    split
    · unfold GenericPopFrame.afterRelevance
      dsimp only [accounted,SourceControl.accounted,Storage.withCurrent]
      rw [fields.terminators]
      dsimp only [helperMachine,RuntimeZeroReturn.entryMachine,RuntimeZeroEntryFacts.completed,Storage.withCurrent]
      unfold GenericPushRelevance.afterPush
      split <;> simp only [CallEntryFacts.cacheTop,CallEntryFacts.freshRoot] <;> repeat' constructor
    · dsimp only [accounted,SourceControl.accounted,Storage.withCurrent]
      rw [fields.terminators]
      dsimp only [helperMachine,RuntimeZeroReturn.entryMachine,RuntimeZeroEntryFacts.completed,Storage.withCurrent]
      unfold GenericPushRelevance.afterPush
      split <;> simp only [CallEntryFacts.cacheTop,CallEntryFacts.freshRoot] <;> repeat' constructor
  have branchKeep : branchMachine.memory = machine.memory ∧
      branchMachine.user.addresses = machine.user.addresses ∧
      branchMachine.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
      branchMachine.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
      branchMachine.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras := by
    rw [branchMachineEq]
    dsimp only [nextUser]
    rw [fields.terminators]
    exact returnedKeep
  have branchMachineActive : ∃ activeThread, branchMachine.threads.activeThread? = some activeThread := by
    obtain ⟨activeThread, active⟩ := parentActive
    exact ⟨activeThread, by simpa [branchMachineEq] using active⟩
  exact ⟨call,afterAssign,afterReturn,deadState,branchState,stepAssign,stepReturn,returnedEq',
    (by simpa [returnedEq'] using stepDead),
    deadLocation,stepBranch,branchLocation,
    ⟨branchFrame,branchMachine,by
      simpa [branchFrame,branchMachine,returnedEq',Storage.withCurrent] using branchStateEq,
      branchFrameBody,branchFrameIdentity,branchFrameCallee,branchFrameLocation,branchFrameSize,
      branchFrameSlot0.1,branchFrameSlot0.2,branchFrameSlot1.1,branchFrameSlot1.2,
      branchFrameSlot2.1,branchFrameSlot2.2,branchFrameNoClocks,branchMachineTracked,
      branchMachineNoRace,defaultMode,branchMachineGhost,branchMachineShallow,
      branchMachineUnchecked,branchMachineNoGc,branchMachineFixed,branchFrameBorrow,branchReturnPlace,branchContinuation,branchVarargs,
      branchKeep.1,branchKeep.2.1,branchKeep.2.2.1,branchKeep.2.2.2.1,branchKeep.2.2.2.2,branchMachineActive⟩⟩

end
end DuplicatePrefix.RuntimeZeroCallStep

open Lean Elab Command in
run_cmd do
  for theoremName in #[``DuplicatePrefix.RuntimeZeroCallStep.call_terminator,
      ``DuplicatePrefix.RuntimeZeroCallStep.call_then_runtime_returns_false,
      ``DuplicatePrefix.RuntimeZeroCallStep.call_runtime_then_parent_false_branch] do
    for dependency in (← collectAxioms theoremName) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError s!"unapproved actual runtime call dependency {dependency} in {theoremName}"
