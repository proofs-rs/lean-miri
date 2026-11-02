import duplicate_prefix.LanguageZeroEntry
import duplicate_prefix.LanguageZeroFunctionFacts
import duplicate_prefix.GuardFunctionConstant
import duplicate_prefix.CallEntryLocals
import duplicate_prefix.GenericCallStages
import duplicate_prefix.CallItemDispatch
import duplicate_prefix.LanguageZeroDispatch


/-! The actual checkLanguage MIR call terminator which enters the zero-argument
    language-runtime helper.  Operand resolution, destination evaluation,
    dispatch and `initStackFrame` are all the production hooks. -/
namespace DuplicatePrefix.LanguageZeroCallStep
open Miri Miri.Input Miri.ABI Miri.MIR Miri.Interpreter Miri.Memory Miri.TreeBorrows
open DuplicatePrefix
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

noncomputable def function : Operand := .Constant GuardFunctionConstant.constant
noncomputable def destination (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra) :=
  (LocalPlaces.localRuntimePlace frames.size caller 5 RootCompilerFacts.boolLayout).stackView
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
    (body : caller.body = CopyPreconditions.Bodies.copyWrapper.loaded.body)
    (identity : caller.bodyIdentity = CopyPreconditions.Bodies.copyWrapper.loaded.identity)
    (callee : caller.functionInstance = CopyPreconditions.Bodies.copyWrapper.fnInstance)
    (location : caller.location = .mir ⟨0,2⟩)
    (callerSize : 5 < caller.locals.size)
    (callerLive : caller.locals[5].value = .live (.immediate .uninit))
    (callerCached : caller.locals[5].layout = some RootCompilerFacts.boolLayout)
    (callerNoClocks : caller.extra.dataRace = none)
    (noRace : machine.dataRace = none)
    (backend : machine.user.payload.payload.user.backend = .none)
    (ghost : machine.user.payload.ghost = false)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (thread : Concurrency.ThreadRecord) (threadIndex : Nat)
    (current : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (LanguageZeroEntryFacts.pushed options.userRelevantCrates
      (Storage.withCurrent frames caller machine) (LanguageZeroEntry.destination frames caller)).stack
      thread.topUserRelevantFrame = some threadIndex)
    (present : (LanguageZeroEntryFacts.pushed options.userRelevantCrates
      (Storage.withCurrent frames caller machine) (LanguageZeroEntry.destination frames caller)).stack.frames[threadIndex]? = some current)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    Call.evalCallTerminator
      (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits)
      () limits.callDispatch
      (CopyPreconditions.Bodies.copyWrapper.loaded.body.basicBlocks[0]'(by with_unfolding_all decide +kernel)).terminator
      (Storage.withCurrent frames caller machine) =
      .ok () (Storage.withCurrent (frames.push caller)
        (LanguageZeroDone.doneFrame (LanguageZeroEntry.rawFrame options (Storage.withCurrent frames caller machine)
          (LanguageZeroEntry.destination frames caller)))
        (LanguageZeroEntry.pushedMachine options (Storage.withCurrent frames caller machine)
          (LanguageZeroEntry.destination frames caller) current)) := by
  let config := PreparedContracts.actualConfig options () (remaining + 1) span
  let h := ExecutionMachine.callHooks config limits
  let state := Storage.withCurrent frames caller machine
  let dest := destination frames caller
  let block := CopyPreconditions.Bodies.copyWrapper.loaded.body.basicBlocks[0]'(by with_unfolding_all decide +kernel)
  let terminator := block.terminator
  have fields := CanonicalConfigFacts.actual_fields options () (remaining + 1) span
  have termKind : terminator.kind =
      .Call function #[] ⟨5,#[]⟩ (some 1) .Continue .Normal ⟨65⟩ := by
    with_unfolding_all rfl
  have blockAt : caller.body.basicBlocks[0]? = some block := by
    rw [body]
    with_unfolding_all rfl
  have noStatement : block.statements[2]? = none := by
    with_unfolding_all rfl
  have functionEval : h.evalOperandAt () (OperandPath.instruction "function") function state =
      .ok ⟨.immediate .uninit,LanguageZeroFunctionFacts.functionLayout⟩ state := by
    change OperandMachine.evalOperandAt (ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits))
      () (OperandPath.instruction "function") function none state = _
    rw [function]
    exact GuardFunctionConstant.function_operand options limits (remaining+1) span source debugOff
      frames caller machine (congrArg (·.index) identity) location callee
  have signature : h.functionSignature () LanguageZeroFunctionFacts.functionLayout =
      pure (0,ABI.ExternAbi.Rust) := by
    change config.calls.compiler.functionSignature () _ = _
    rw [fields.callCompiler]
    simp only [CompilerCallConstruction.compiler,CompilerExecutionCallLeaves.make]
    rw [LanguageZeroFunctionFacts.functionLayout_shape.1,LanguageZeroFunctionFacts.function_signature_query]
    simp only [bind,Except.bind,pure,Except.pure]
    rw [LanguageZeroFunctionFacts.decode_rust_extern_abi cmp]
    with_unfolding_all rfl
  have kind : h.functionKind LanguageZeroFunctionFacts.functionLayout.ty =
      pure (.FnDef 13 #[]) := by
    change config.calls.compiler.functionKind _ = _
    rw [fields.callCompiler]
    with_unfolding_all change (match CompilerFunctionFacts.kind PreparedReflection.actual.compiler.functions
      LanguageZeroFunctionFacts.functionLayout.ty with
      | .ok value => pure value
      | .error reason => throw (.unsupported reason) :
        MachineHooks.M MiriMemoryKind Machine.RootUser CallFunctionKind) = _
    rw [LanguageZeroFunctionFacts.functionLayout_shape.1,LanguageZeroFunctionFacts.function_kind]
  have resolve : h.resolve () 13 #[] state = .ok GuardCompilerFacts.languageCall.callee state := by
    change config.calls.compiler.resolve () 13 #[] state = _
    rw [fields.callCompiler]
    exact LanguageZeroFunctionFacts.resolve_current frames caller machine body identity callee location
  have itemKind : GuardCompilerFacts.languageCall.callee.kind = .Item 13 := by
    rw [LanguageZeroFunctionFacts.function_kind_matches_call]
  have fnAbi : h.fnAbiOfInstance () GuardCompilerFacts.languageCall.callee #[] = pure GuardCompilerFacts.languageAbi := by
    funext st
    exact GuardCompilerFacts.actual_language_abi options () (remaining+1) span st
  have callerLocation : h.requiresCallerLocation GuardCompilerFacts.languageCall.callee = pure false := by
    funext st
    exact GuardCompilerFacts.actual_language_caller_location options () (remaining+1) span limits st
  have calleeEval := GenericCallStages.eval_callee_zero h () function ⟨5,#[]⟩
    ⟨.immediate .uninit,LanguageZeroFunctionFacts.functionLayout⟩ state state .Rust 13 #[]
    GuardCompilerFacts.languageCall.callee 13 GuardCompilerFacts.languageAbi false
    functionEval signature kind resolve itemKind fnAbi callerLocation
  have destinationEval := CallEntryLocals.destination_cached options limits (remaining+1) span debugOff
    frames caller machine 5 RootCompilerFacts.boolLayout callerSize callerCached (by decide +kernel)
  have destEq : dest = LanguageZeroEntry.destination frames caller := by rfl
  have destinationEval' : h.evalPlace () ⟨5,#[]⟩ false state = .ok dest state := by
    exact destinationEval
  let call : EvaluatedCall Provenance Unit ABI.ExternAbi (FnAbi TyId) :=
    ⟨.Instance GuardCompilerFacts.languageCall.callee,#[],.Rust,some GuardCompilerFacts.languageAbi,false⟩
  have calleeEval' : Call.evalCalleeAndArgs h () function #[] ⟨5,#[]⟩ state = .ok call state := by
    simpa [call,dest,destination] using calleeEval
  let after := Storage.withCurrent (frames.push caller)
    (LanguageZeroDone.doneFrame (LanguageZeroEntry.rawFrame options state (LanguageZeroEntry.destination frames caller)))
    (LanguageZeroEntry.pushedMachine options state (LanguageZeroEntry.destination frames caller) current)
  let request : CallRequest Provenance Unit ABI.ExternAbi (FnAbi TyId) :=
    ⟨.Instance GuardCompilerFacts.languageCall.callee,.Rust,some GuardCompilerFacts.languageAbi,#[],false,
      LanguageZeroEntry.destination frames caller,some 1,.Continue⟩
  have find := LanguageZeroDispatch.find_mir options limits (remaining+1) span state #[]
    (LanguageZeroEntry.destination frames caller) (some 1) .Continue backend noRace
  have canUnwind : h.abiCanUnwind GuardCompilerFacts.languageAbi = true := by
    change GuardCompilerFacts.languageAbi.canUnwind = true
    exact congrArg (fun x => x.2.2.2.2.2) GuardCompilerFacts.language_abi_shape
  have abiEq : GuardCompilerFacts.languageAbi = GuardCompilerFacts.languageAbi := by rfl
  have rustCall : h.isRustCall ABI.ExternAbi.Rust = false := by
    change config.calls.compiler.isRustCall .Rust = false
    rw [fields.callCompiler]
    rfl
  have dispatchStep : Call.initFnCallStep h () request state = .ok none after := by
    have item := CallItemDispatch.item_step h GuardCompilerFacts.languageCall.callee 13 GuardCompilerFacts.languageAbi
      #[] false (LanguageZeroEntry.destination frames caller) (some 1) .Continue .Rust itemKind canUnwind rustCall
    rw [item]
    simp only [CallItemDispatch.itemStage, bind, EStateM.bind]
    have find' := find
    change h.findMirOrEvalFn () GuardCompilerFacts.languageCall.callee GuardCompilerFacts.languageAbi #[]
      (LanguageZeroEntry.destination frames caller) (some 1) .Continue state = _ at find'
    rw [find']
    simp only [bind, EStateM.bind, pure, EStateM.pure]
    have enter := LanguageZeroEntry.actual_entry options limits remaining span debugOff frames caller machine
      callerSize callerLive callerCached callerNoClocks noRace ghost tracker tracked thread threadIndex current active top present
    have enter' : Call.initStackFrame h () GuardCompilerFacts.languageCall.callee
        CopyPreconditions.Bodies.checkLanguage.loaded GuardCompilerFacts.languageAbi #[] false
        (LanguageZeroEntry.destination frames caller) (.goto (some 1) .Continue)
        (Storage.withCurrent frames caller machine) = .ok ()
        (Storage.withCurrent (frames.push caller)
          (LanguageZeroDone.doneFrame (LanguageZeroEntry.rawFrame options
            (Storage.withCurrent frames caller machine) (LanguageZeroEntry.destination frames caller)))
          (LanguageZeroEntry.pushedMachine options (Storage.withCurrent frames caller machine)
            (LanguageZeroEntry.destination frames caller) current)) := by
      rw [← abiEq]
      exact enter
    rw [enter']
  have init : Call.initFnCall h () limits.callDispatch request state = .ok () after := by
    have step := CallItemDispatch.dispatch_one h request state after budget dispatchStep
    simpa [dispatchFuel] using step
  have init' : Call.initFnCall h () limits.callDispatch
      ⟨call.callee,call.callerAbi,call.fnAbi,call.args,call.withCallerLocation,
        LanguageZeroEntry.destination frames caller,some 1,
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
  exact GenericCallStages.call_terminator h () limits.callDispatch block.terminator function #[] ⟨5,#[]⟩
    1 .Continue .Normal ⟨65⟩ state state state after caller frames.size (frames.size+1)
    (LanguageZeroEntry.destination frames caller) call termKind getFrame oldIndex
    (by simpa [destEq] using destinationEval') calleeEval' init' newIndex progress


end
end DuplicatePrefix.LanguageZeroCallStep

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.LanguageZeroCallStep.call_terminator) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved language call dependency {dependency}"
