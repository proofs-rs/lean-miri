import duplicate_prefix.CanonicalConfigFacts
import duplicate_prefix.Storage
import duplicate_prefix.SpanFacts

/-! Actual canonical call-entry compiler queries. These facts are the static
prefix of full argument installation and FnEntry retagging; no entry safety
or operational success is postulated. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace DuplicatePrefix.CallEntryFacts
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory

noncomputable def config := PreparedContracts.actualConfig

theorem actual_root_abi (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (config options choice remaining span).calls.compiler.fnAbiOfInstance choice
      RootBody.reflected.functionInstance #[] state = .ok RootCompilerFacts.rootAbi state := by
  unfold config
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).callCompiler]
  with_unfolding_all change (match RootCompilerFacts.rootAbiQuery with
    | .ok value => pure value
    | .error reason => throw (StepError.unsupported reason) : MachineHooks.M MiriMemoryKind Machine.RootUser (FnAbi MIR.TyId)) state = _
  rw [RootCompilerFacts.root_abi_eq]
  rfl

theorem actual_root_load_mir (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (config options choice remaining span).helpers.loadMir choice
      RootBody.reflected.functionInstance state = .ok RootBody.reflected.body state := by
  unfold config
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).loadMir]
  with_unfolding_all change (match CallResolution.loadedBodyOfInstance PreparedReflection.actual.compiler.lifecycle.calls.calls
      RootBody.reflected.functionInstance with
    | .ok value => pure value
    | .error reason => throw (StepError.unsupported s!"compiler call pipeline: {reason}") : MachineHooks.M MiriMemoryKind Machine.RootUser LoadedBody) state = _
  rw [PreparedContracts.fixed_root_loaded]
  rfl

theorem root_requires_no_caller_location :
    CompilerRuntimeQueries.requiresCallerLocation PreparedReflection.actual.compiler.lifecycle.calls.runtime
      RootBody.reflected.functionInstance = .ok false := by with_unfolding_all rfl

theorem root_required_target_features :
    CompilerTargetFeatures.required PreparedReflection.actual.compiler.intrinsics
      RootBody.reflected.functionInstance = .ok #[] := by with_unfolding_all rfl

theorem root_not_closure_like :
    CompilerCallFacts.isClosureLike PreparedReflection.actual.compiler.intrinsics
      RootBody.reflected.functionInstance = .ok false := by with_unfolding_all rfl

theorem actual_call_hooks_root_abi (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (limits : ExecutionMachine.Limits)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (ExecutionMachine.callHooks (config options choice remaining span) limits).fnAbiOfInstance choice
      RootBody.reflected.functionInstance #[] state = .ok RootCompilerFacts.rootAbi state := by
  change (config options choice remaining span).calls.compiler.fnAbiOfInstance choice
    RootBody.reflected.functionInstance #[] state = _
  exact actual_root_abi options choice remaining span state

theorem actual_call_hooks_requires_no_caller_location (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (limits : ExecutionMachine.Limits)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (ExecutionMachine.callHooks (config options choice remaining span) limits).requiresCallerLocation
      RootBody.reflected.functionInstance state = .ok false state := by
  change (config options choice remaining span).virtual.compiler.requiresCallerLocation
    RootBody.reflected.functionInstance state = _
  unfold config
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).virtualCompiler]
  with_unfolding_all change (match CompilerRuntimeQueries.requiresCallerLocation
      PreparedReflection.actual.compiler.lifecycle.calls.runtime RootBody.reflected.functionInstance with
    | .ok value => pure value
    | .error reason => throw (StepError.unsupported s!"compiler virtual query: {reason}") :
      MachineHooks.M MiriMemoryKind Machine.RootUser Bool) state = _
  rw [root_requires_no_caller_location]
  rfl

theorem actual_call_hooks_non_capturing_false (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (limits : ExecutionMachine.Limits)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (ExecutionMachine.callHooks (config options choice remaining span) limits).nonCapturingClosure choice
      RootBody.reflected.functionInstance RootCompilerFacts.rootAbi state = .ok false state := by
  change ExecutionCallLeaves.nonCapturingClosure (config options choice remaining span).calls.compiler
    RootBody.reflected.functionInstance RootCompilerFacts.rootAbi state = _
  unfold config
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).callCompiler]
  have query : (CompilerCallConstruction.compiler (C := Unit) PreparedReflection.actual.compiler
      options.compatibilityBudget).isClosureLike RootBody.reflected.functionInstance =
      (pure false : MachineHooks.M MiriMemoryKind Machine.RootUser Bool) := by
    with_unfolding_all change (match CompilerCallFacts.isClosureLike PreparedReflection.actual.compiler.intrinsics
        RootBody.reflected.functionInstance with
      | .ok value => pure value
      | .error reason => throw (StepError.unsupported reason) :
        MachineHooks.M MiriMemoryKind Machine.RootUser Bool) = _
    rw [root_not_closure_like]
  unfold ExecutionCallLeaves.nonCapturingClosure
  simp only [RootBody.reflected] at query ⊢
  rw [query]
  rfl

theorem actual_call_hooks_target_features (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (limits : ExecutionMachine.Limits)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (ExecutionMachine.callHooks (config options choice remaining span) limits).checkTargetFeatures choice
      RootBody.reflected.functionInstance state = .ok () state := by
  change ExecutionCallLeaves.checkTargetFeatures
    (config options choice remaining span).calls.compiler.targetFeatures
    RootBody.reflected.functionInstance state = _
  unfold config
  rw [(CanonicalConfigFacts.actual_fields options choice remaining span).callCompiler]
  have query : (CompilerCallConstruction.compiler (C := Unit) PreparedReflection.actual.compiler
      options.compatibilityBudget).targetFeatures.required RootBody.reflected.functionInstance =
      (pure #[] : MachineHooks.M MiriMemoryKind Machine.RootUser (Array ExecutionCallLeaves.TargetFeature)) := by
    with_unfolding_all change (match CompilerTargetFeatures.required PreparedReflection.actual.compiler.intrinsics
        RootBody.reflected.functionInstance with
      | .ok value => pure value
      | .error reason => throw (StepError.unsupported reason) :
        MachineHooks.M MiriMemoryKind Machine.RootUser (Array ExecutionCallLeaves.TargetFeature)) = _
    rw [root_required_target_features]
  unfold ExecutionCallLeaves.checkTargetFeatures
  rw [query]
  rfl

theorem root_abi_entry_flags :
    RootCompilerFacts.rootAbi.cVariadic = false ∧
    RootCompilerFacts.rootAbi.canUnwind = true ∧
    RootCompilerFacts.rootAbi.args.size = 2 ∧
    RootCompilerFacts.rootAbi.conv = .Rust := by decide +kernel

theorem root_body_entry_flags :
    RootBody.reflected.body.body.argumentCount = 2 ∧
    RootBody.reflected.body.body.spreadArgument = none := by decide +kernel

theorem root_return_argument_compat {S : Type} (queries : LayoutCompat.Queries MIR.TyId S)
    (budget : Nat) (state : S) :
    LayoutCompat.checkArgumentCompat queries budget RootCompilerFacts.rootAbi.ret
      RootCompilerFacts.rootAbi.ret state = .ok true state := by with_unfolding_all rfl

theorem root_slice_argument_compat {S : Type} (queries : LayoutCompat.Queries MIR.TyId S)
    (budget : Nat) (state : S) :
    LayoutCompat.checkArgumentCompat queries budget (RootCompilerFacts.rootAbi.args.getD 0 RootCompilerFacts.rootAbi.ret)
      (RootCompilerFacts.rootAbi.args.getD 0 RootCompilerFacts.rootAbi.ret) state = .ok true state := by with_unfolding_all rfl

theorem root_usize_argument_compat {S : Type} (queries : LayoutCompat.Queries MIR.TyId S)
    (budget : Nat) (state : S) :
    LayoutCompat.checkArgumentCompat queries budget (RootCompilerFacts.rootAbi.args.getD 1 RootCompilerFacts.rootAbi.ret)
      (RootCompilerFacts.rootAbi.args.getD 1 RootCompilerFacts.rootAbi.ret) state = .ok true state := by with_unfolding_all rfl

theorem root_preamble_span {K User : Type} (state : MachineHooks.State K User) :
    CompilerLifecycle.preambleSpan PreparedReflection.actual.compiler.lifecycle.lifecycle
      RootBody.reflected.body state = .ok ⟨559⟩ state := by with_unfolding_all rfl

theorem root_required_constants (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    CompilerLifecycle.requiredConstants PreparedReflection.actual.compiler.lifecycle.lifecycle
      RootBody.reflected.body (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore frame machine) := by
  with_unfolding_all change ((do
    let frame ← MachineHooks.currentFrame
    unless frame.bodyIdentity == RootBody.reflected.body.identity &&
        frame.functionInstance == RootBody.reflected.functionInstance do
      throw (StepError.invalidProgram "required-constant current frame identity/instance mismatch")
    pure () : MachineHooks.M MiriMemoryKind Machine.RootUser Unit)
      (Storage.withCurrent framesBefore frame machine)) = _
  simp only [MachineHooks.currentFrame, Storage.withCurrent, Stack.currentFrame?, Array.back?_push,
    bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
    pure, EStateM.pure, identity, callee]
  with_unfolding_all rfl

theorem root_user_relevance {K User Extra : Type} (crates : Array Nat)
    (frame : Frame Provenance LocalLayout Extra) (state : MachineHooks.State K User)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    FrameMetadata.userRelevance
      (CompilerFrameMetadata.hooks PreparedReflection.actual.compiler.lifecycle.frames crates)
      frame state = .ok 255 state := by
  unfold FrameMetadata.userRelevance
  rw [callee]
  with_unfolding_all rfl

noncomputable def rawRootFrame (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (destination : RuntimeStackPlace Provenance) (identity : LocalsIdentity) :
    Frame Provenance LocalLayout MachineHooks.FrameExtra :=
  let frame : Frame Provenance LocalLayout Unit := Frame.create RootBody.reflected.body
    RootBody.reflected.functionInstance () (.stop true) destination ⟨559⟩ identity
  { body := frame.body, bodyIdentity := frame.bodyIdentity, functionInstance := frame.functionInstance
    extra := {borrowTracker := machine.borrowTracker.map (fun _ => {}), catchUnwind := none, userRelevance := 255, dataRace := machine.dataRace.map (fun _ => {})}
    returnContinuation := frame.returnContinuation, returnPlace := frame.returnPlace
    localsIdentity := frame.localsIdentity, locals := frame.locals, vaList := frame.vaList
    trackCallerArg := frame.trackCallerArg, location := frame.location }

theorem init_root_frame (crates : Array Nat)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (destination : RuntimeStackPlace Provenance) (identity : LocalsIdentity) :
    MachineHooks.initFrame (FrameMetadata.userRelevance
      (CompilerFrameMetadata.hooks PreparedReflection.actual.compiler.lifecycle.frames crates))
      (Frame.create RootBody.reflected.body RootBody.reflected.functionInstance ()
        (.stop true) destination ⟨559⟩ identity) state =
      .ok (rawRootFrame state.machine destination identity) state := by
  unfold MachineHooks.initFrame
  have relevance := root_user_relevance crates
    (Frame.create RootBody.reflected.body RootBody.reflected.functionInstance ()
      (.stop true) destination ⟨559⟩ identity : Frame Provenance LocalLayout Unit) state rfl
  simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
    pure, EStateM.pure] at relevance ⊢
  rw [relevance]
  rfl

open Lean Elab Tactic in
elab "unfold_relevance_helpers" : tactic => do
  let env ← getEnv
  let suffixes := [".FrameRelevance.active", ".FrameRelevance.setCache"]
  let names ← suffixes.mapM fun (suffix : String) => do
    let candidates := env.constants.toList.filterMap fun (name, _) =>
      if name.toString.endsWith suffix then some (mkIdent name) else none
    match candidates with
    | [name] => pure name
    | _ => throwError "expected exact source relevance helper {suffix}"
  let names := names.toArray
  evalTactic (← `(tactic| simp only [$[$names:ident],*]))

def cacheTop (machine : MachineHooks.MachineState K User) (index : Nat) :=
  { machine with threads := { machine.threads with threads := machine.threads.threads.mapIdx (fun position (thread : Miri.Concurrency.ThreadRecord) =>
      if position == machine.threads.activeThread.toNat then
        {thread with topUserRelevantFrame := some index} else thread) } }

theorem relevance_after_push (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K User) (thread : Miri.Concurrency.ThreadRecord)
    (active : machine.threads.activeThread? = some thread)
    (noCache : thread.topUserRelevantFrame = none) :
    FrameRelevance.afterStackPush false (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore frame (cacheTop machine framesBefore.size)) := by
  unfold FrameRelevance.afterStackPush
  unfold_relevance_helpers
  simp [MachineHooks.currentFrame, Storage.withCurrent, Stack.currentFrame?,
    Array.back?_push, active, noCache, FrameRelevance.top,
    bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    pure, EStateM.pure, cacheTop]

def freshRoot (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :
    MachineHooks.MachineState MiriMemoryKind Machine.RootUser × LocalsIdentity :=
  let allocated := (EvalConfiguration.identity.get machine.user).allocate
  ({machine with user := EvalConfiguration.identity.put machine.user allocated.1}, allocated.2)

noncomputable def rawPushedState
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (destination : RuntimeStackPlace Provenance) : MachineHooks.State MiriMemoryKind Machine.RootUser :=
  let fresh := freshRoot machine
  Storage.withCurrent framesBefore (rawRootFrame fresh.1 destination fresh.2)
    (cacheTop fresh.1 framesBefore.size)

theorem actual_push_raw_root (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (destination : RuntimeStackPlace Provenance) (thread : Miri.Concurrency.ThreadRecord)
    (active : state.machine.threads.activeThread? = some thread)
    (noCache : thread.topUserRelevantFrame = none) :
    CallMachine.pushRaw (config options choice remaining span).lifecycle false
      RootBody.reflected.functionInstance RootBody.reflected.body destination (.stop true) state =
      .ok () (rawPushedState state.stack.frames state.machine destination) := by
  unfold config CallMachine.pushRaw
  have fields := CanonicalConfigFacts.actual_fields options choice remaining span
  rw [fields.freshLocalsIdentity, fields.preambleSpan, fields.frameCompiler, fields.requiredConstants]
  simp only [Bool.false_and, Bool.false_eq_true, ite_false,
    bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
    set, MonadStateOf.set, EStateM.set,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  rw [root_preamble_span]
  dsimp only
  rw [init_root_frame]
  dsimp only
  let fresh := freshRoot state.machine
  have checks := root_required_constants state.stack.frames
    (rawRootFrame fresh.1 destination fresh.2) fresh.1 rfl rfl
  dsimp only [fresh, freshRoot, Storage.withCurrent] at checks
  rw [checks]
  have freshActive : fresh.1.threads.activeThread? = some thread := active
  simpa only [rawPushedState, fresh, freshRoot, Storage.withCurrent] using
    relevance_after_push state.stack.frames (rawRootFrame fresh.1 destination fresh.2)
      fresh.1 thread freshActive noCache

theorem root_local4_normalized (frame : CompilerFrameContext.ActualFrame)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler frame 4 = .ok 0 := by
  unfold CompilerFrameContext.normalizedLocalType CompilerFrameContext.normalizedBody CompilerFrameContext.bodyOfFrame
  rw [body, identity, callee]
  with_unfolding_all rfl

theorem actual_call_hooks_push_raw (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (limits : ExecutionMachine.Limits) (noDebug : options.place.debugAssertions = false)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (destination : RuntimeStackPlace Provenance) (thread : Miri.Concurrency.ThreadRecord)
    (active : state.machine.threads.activeThread? = some thread)
    (noCache : thread.topUserRelevantFrame = none) :
    (ExecutionMachine.callHooks (config options choice remaining span) limits).pushRaw choice
      RootBody.reflected.functionInstance RootBody.reflected.body destination (.stop true) state =
      .ok () (rawPushedState state.stack.frames state.machine destination) := by
  change CallMachine.pushRaw (config options choice remaining span).lifecycle
    (config options choice remaining span).compiler.debugAssertions
    RootBody.reflected.functionInstance RootBody.reflected.body destination (.stop true) state = _
  have debug := (CanonicalConfigFacts.actual_fields options choice remaining span).debug
  unfold config at debug ⊢
  rw [debug, noDebug]
  exact actual_push_raw_root options choice remaining span state destination thread active noCache

theorem root_compute_local4
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler 4
      (Storage.withCurrent framesBefore frame machine) =
      .ok RootCompilerFacts.boolLayout (Storage.withCurrent framesBefore frame machine) := by
  have normalized := root_local4_normalized frame body identity callee
  unfold CompilerFrameContext.computeLocalLayout
  simp only [MachineHooks.currentFrame, Storage.withCurrent, Stack.currentFrame?, Array.back?_push,
    bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]
  rw [normalized]
  with_unfolding_all change (match PreparedReflection.actual.runtime.lookup 0 with
    | .ok value => EStateM.Result.ok value (Storage.withCurrent framesBefore frame machine)
    | .error error => EStateM.Result.error (StepError.unsupported s!"compiler frame query: {toString error}")
        (Storage.withCurrent framesBefore frame machine)) = _
  rw [RootCompilerFacts.bool_layout_eq]
  rfl

theorem root_local0_normalized (frame : CompilerFrameContext.ActualFrame)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler frame 0 = .ok 0 := by
  unfold CompilerFrameContext.normalizedLocalType CompilerFrameContext.normalizedBody CompilerFrameContext.bodyOfFrame
  rw [body, identity, callee]
  with_unfolding_all rfl

theorem root_local1_normalized (frame : CompilerFrameContext.ActualFrame)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler frame 1 = .ok 3 := by
  unfold CompilerFrameContext.normalizedLocalType CompilerFrameContext.normalizedBody CompilerFrameContext.bodyOfFrame
  rw [body, identity, callee]
  with_unfolding_all rfl

theorem root_local2_normalized (frame : CompilerFrameContext.ActualFrame)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler frame 2 = .ok 5 := by
  unfold CompilerFrameContext.normalizedLocalType CompilerFrameContext.normalizedBody CompilerFrameContext.bodyOfFrame
  rw [body, identity, callee]
  with_unfolding_all rfl

open Lean Elab Tactic in
elab "unfold_frame_query_lift" : tactic => do
  let env ← getEnv
  let candidates := env.constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith ".CompilerFrameContext.lift" then some (mkIdent name) else none
  let [name] := candidates | throwError "expected exact source compiler-frame lift"
  evalTactic (← `(tactic| simp only [$name:ident]))

private theorem compute_local_from_metadata (compiler : CompilerProviders.Prepared)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState K User)
    (localId ty : Nat) (layout : LocalLayout)
    (normalized : CompilerFrameContext.normalizedLocalType compiler frame localId = .ok ty)
    (queried : compiler.runtime.lookup ty = .ok layout) :
    CompilerFrameContext.computeLocalLayout compiler localId (Storage.withCurrent framesBefore frame machine) =
      .ok layout (Storage.withCurrent framesBefore frame machine) := by
  unfold CompilerFrameContext.computeLocalLayout
  simp only [MachineHooks.currentFrame, Storage.withCurrent, Stack.currentFrame?, Array.back?_push,
    bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]
  rw [normalized]
  unfold_frame_query_lift
  simp only [pure, EStateM.pure]
  rw [queried]
  rfl

theorem root_compute_local0
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState K User)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler 0
      (Storage.withCurrent framesBefore frame machine) =
      .ok RootCompilerFacts.boolLayout (Storage.withCurrent framesBefore frame machine) :=
  compute_local_from_metadata _ _ _ _ 0 0 _
    (root_local0_normalized frame body identity callee) RootCompilerFacts.bool_layout_eq

theorem root_compute_local1
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState K User)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler 1
      (Storage.withCurrent framesBefore frame machine) =
      .ok RootCompilerFacts.sliceLayout (Storage.withCurrent framesBefore frame machine) :=
  compute_local_from_metadata _ _ _ _ 1 3 _
    (root_local1_normalized frame body identity callee) RootCompilerFacts.slice_layout_eq

theorem root_compute_local2
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState K User)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler 2
      (Storage.withCurrent framesBefore frame machine) =
      .ok RootCompilerFacts.usizeLayout (Storage.withCurrent framesBefore frame machine) :=
  compute_local_from_metadata _ _ _ _ 2 5 _
    (root_local2_normalized frame body identity callee) RootCompilerFacts.usize_layout_eq

theorem root_always_live :
    CallMachine.alwaysLiveVarsAndTemps RootBody.reflected.body.body = .ok #[6, 13, 14] := by
  with_unfolding_all rfl

def liveSlot (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (localId : Nat) :=
  {frame with locals := frame.locals.modify localId (fun slot => {slot with value := .live (.immediate .uninit)})}

private theorem storage_live_slot (hooks : MachineHooks.StorageHooks K User)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K User) (localId : MIR.LocalId) (ty : MIR.TyId)
    (valid : localId < frame.locals.size) (typed : frame.body.locals[localId]? = some ty)
    (trivial : hooks.veryTriviallySized ty = .ok true)
    (dead : frame.locals[localId].value = .dead) (noClocks : frame.extra.dataRace = none) :
    MachineHooks.storageLiveDyn hooks localId .none (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore (liveSlot frame localId) machine) := by
  have step := Storage.storage_live_dead hooks framesBefore frame machine localId ty
    valid typed trivial dead noClocks
  simpa [liveSlot, Array.modify, Array.modifyM, valid] using step

def doneRootFrame (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) :=
  { (liveSlot (liveSlot (liveSlot (liveSlot frame 0) 6) 13) 14) with location := .mir .start }

private theorem root_start_location (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (body : frame.body = RootBody.reflected.body.body) :
    frame.setLocation (.mir .start) = .ok {frame with location := .mir .start} := by
  unfold Frame.setLocation
  rw [body]
  with_unfolding_all rfl

private theorem stack_start_location
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (body : frame.body = RootBody.reflected.body.body) :
    (⟨framesBefore.push frame⟩ : Stack Provenance LocalLayout MachineHooks.FrameExtra).updateCurrentLocation
      (.mir .start) = .ok ⟨framesBefore.push {frame with location := .mir .start}⟩ := by
  simp [Stack.updateCurrentLocation, root_start_location frame body, Array.set_push]
  rfl

private theorem push_done_root (lifecycle : CallMachine.Lifecycle K User C)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K User)
    (body : frame.body = RootBody.reflected.body.body) (size : frame.locals.size = 25)
    (dead0 : (frame.locals[0]'(by omega)).value = .dead)
    (dead6 : (frame.locals[6]'(by omega)).value = .dead)
    (dead13 : (frame.locals[13]'(by omega)).value = .dead)
    (dead14 : (frame.locals[14]'(by omega)).value = .dead)
    (noClocks : frame.extra.dataRace = none)
    (trivialBool : lifecycle.storage.veryTriviallySized 0 = .ok true)
    (trivialNever : lifecycle.storage.veryTriviallySized 6 = .ok true) :
    CallMachine.pushDone lifecycle (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore (doneRootFrame frame) machine) := by
  let f0 := liveSlot frame 0
  let f6 := liveSlot f0 6
  let f13 := liveSlot f6 13
  let f14 := liveSlot f13 14
  have h0 := storage_live_slot lifecycle.storage framesBefore frame machine 0 0
    (by rw [size]; decide) (by rw [body]; rfl) trivialBool dead0 noClocks
  have h6 := storage_live_slot lifecycle.storage framesBefore f0 machine 6 6
    (by simpa [f0, liveSlot] using (show 6 < frame.locals.size by omega))
    (by simp only [f0, liveSlot, body]; rfl) trivialNever
    (by simpa [f0, liveSlot, Array.getElem_modify] using dead6) noClocks
  have h13 := storage_live_slot lifecycle.storage framesBefore f6 machine 13 0
    (by simpa [f6, f0, liveSlot] using (show 13 < frame.locals.size by omega))
    (by simp only [f6, f0, liveSlot, body]; rfl) trivialBool
    (by simpa [f6, f0, liveSlot, Array.getElem_modify] using dead13) noClocks
  have h14 := storage_live_slot lifecycle.storage framesBefore f13 machine 14 6
    (by simpa [f13, f6, f0, liveSlot] using (show 14 < frame.locals.size by omega))
    (by simp only [f13, f6, f0, liveSlot, body]; rfl) trivialNever
    (by simpa [f13, f6, f0, liveSlot, Array.getElem_modify] using dead14) noClocks
  dsimp only [f0, f6, f13] at h6 h13 h14
  unfold CallMachine.pushDone
  simp only [bind, EStateM.bind]
  rw [h0]
  dsimp only
  rw [Storage.current_frame]
  dsimp only
  have always : CallMachine.alwaysLiveVarsAndTemps f0.body = .ok #[6, 13, 14] := by
    simpa only [f0, liveSlot, body] using root_always_live
  rw [always]
  simp only [pure]
  simp [← Array.forIn_toList, bind, EStateM.bind, pure, EStateM.pure,
    h6, h13, h14]
  simp only [get, getThe, MonadStateOf.get, EStateM.get]
  simp only [Storage.withCurrent]
  rw [stack_start_location framesBefore _ (by simpa only [liveSlot] using body)]
  rfl


theorem actual_push_done_root (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = RootBody.reflected.body.body) (size : frame.locals.size = 25)
    (dead0 : (frame.locals[0]'(by omega)).value = .dead)
    (dead6 : (frame.locals[6]'(by omega)).value = .dead)
    (dead13 : (frame.locals[13]'(by omega)).value = .dead)
    (dead14 : (frame.locals[14]'(by omega)).value = .dead)
    (noClocks : frame.extra.dataRace = none) :
    CallMachine.pushDone (config options choice remaining span).lifecycle
      (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore (doneRootFrame frame) machine) := by
  apply push_done_root _ _ _ _ body size dead0 dead6 dead13 dead14 noClocks
  · exact CanonicalConfigFacts.actual_storage_bool options choice remaining span
  · unfold config
    rw [(CanonicalConfigFacts.actual_fields options choice remaining span).storage]
    exact RootCompilerFacts.root_storage_trivial_never

theorem actual_call_hooks_push_done (options : EvalConfigurationCore.Options)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (limits : ExecutionMachine.Limits)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = RootBody.reflected.body.body) (size : frame.locals.size = 25)
    (dead0 : (frame.locals[0]'(by omega)).value = .dead)
    (dead6 : (frame.locals[6]'(by omega)).value = .dead)
    (dead13 : (frame.locals[13]'(by omega)).value = .dead)
    (dead14 : (frame.locals[14]'(by omega)).value = .dead)
    (noClocks : frame.extra.dataRace = none) :
    (ExecutionMachine.callHooks (config options choice remaining span) limits).pushDone choice
      (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore (doneRootFrame frame) machine) := by
  change CallMachine.pushDone (config options choice remaining span).lifecycle _ = _
  exact actual_push_done_root options choice remaining span framesBefore frame machine body size
    dead0 dead6 dead13 dead14 noClocks

private theorem root_body_of_frame (frame : CompilerFrameContext.ActualFrame)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    CompilerFrameContext.bodyOfFrame PreparedReflection.actual.compiler frame = .ok SpanFacts.rootInputBody := by
  unfold CompilerFrameContext.bodyOfFrame
  rw [body, identity, callee]
  with_unfolding_all rfl

private theorem local_span_from_metadata (compiler : CompilerProviders.Prepared)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState K User)
    (supplied : MIR.Body) (localId : Nat) (source : LoweredBody) (decl : Input.LocalDecl)
    (spanData : SourceSpanData) (index : Nat)
    (sameBody : supplied = frame.body)
    (sourceBody : CompilerFrameContext.bodyOfFrame compiler frame = .ok source)
    (sourceDecl : source.input.locals[localId]? = some decl)
    (declSpan : decl.sourceInfo.span = spanData)
    (lookupSpan : compiler.program.bundle.spans.toList.idxOf? spanData = some index) :
    CompilerFrameContext.localSpan compiler supplied localId (Storage.withCurrent framesBefore frame machine) =
      .ok ⟨index⟩ (Storage.withCurrent framesBefore frame machine) := by
  unfold CompilerFrameContext.localSpan
  simp only [MachineHooks.currentFrame, Storage.withCurrent, Stack.currentFrame?, Array.back?_push,
    bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]
  rw [sameBody]
  simp only [beq_self_eq_true, ite_true]
  rw [sourceBody]
  unfold_frame_query_lift
  simp only [EStateM.bind, pure, EStateM.pure]
  rw [sourceDecl]
  dsimp only
  rw [declSpan, lookupSpan]
  rfl

theorem root_local0_span
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState K User)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    CompilerFrameContext.localSpan PreparedReflection.actual.compiler RootBody.reflected.body.body 0
      (Storage.withCurrent framesBefore frame machine) =
      .ok ⟨601⟩ (Storage.withCurrent framesBefore frame machine) := by
  have valid : 0 < SpanFacts.rootInputBody.input.locals.size := by decide +kernel
  let decl := SpanFacts.rootInputBody.input.locals[0]'valid
  have present : SpanFacts.rootInputBody.input.locals[0]? = some decl := by
    simp [decl, valid]
  have spanQuery : PreparedReflection.actual.compiler.program.bundle.spans.toList.idxOf?
      (SpanFacts.rootLocalSpan ⟨0, by decide⟩) = some 601 := by
    rw [show PreparedReflection.actual.compiler.program = PreparedReflection.actual.program by rfl]
    exact SpanFacts.root_local0_span_index
  exact local_span_from_metadata _ _ _ _ _ _ SpanFacts.rootInputBody decl _ 601 body.symm
    (root_body_of_frame frame body identity callee) present rfl spanQuery

theorem root_local1_span
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState K User)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    CompilerFrameContext.localSpan PreparedReflection.actual.compiler RootBody.reflected.body.body 1
      (Storage.withCurrent framesBefore frame machine) =
      .ok ⟨602⟩ (Storage.withCurrent framesBefore frame machine) := by
  have valid : 1 < SpanFacts.rootInputBody.input.locals.size := by decide +kernel
  let decl := SpanFacts.rootInputBody.input.locals[1]'valid
  have present : SpanFacts.rootInputBody.input.locals[1]? = some decl := by
    simp [decl, valid]
  have spanQuery : PreparedReflection.actual.compiler.program.bundle.spans.toList.idxOf?
      (SpanFacts.rootLocalSpan ⟨1, by decide⟩) = some 602 := by
    rw [show PreparedReflection.actual.compiler.program = PreparedReflection.actual.program by rfl]
    exact SpanFacts.root_local1_span_index
  exact local_span_from_metadata _ _ _ _ _ _ SpanFacts.rootInputBody decl _ 602 body.symm
    (root_body_of_frame frame body identity callee) present rfl spanQuery

theorem root_local2_span
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState K User)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    CompilerFrameContext.localSpan PreparedReflection.actual.compiler RootBody.reflected.body.body 2
      (Storage.withCurrent framesBefore frame machine) =
      .ok ⟨603⟩ (Storage.withCurrent framesBefore frame machine) := by
  have valid : 2 < SpanFacts.rootInputBody.input.locals.size := by decide +kernel
  let decl := SpanFacts.rootInputBody.input.locals[2]'valid
  have present : SpanFacts.rootInputBody.input.locals[2]? = some decl := by
    simp [decl, valid]
  have spanQuery : PreparedReflection.actual.compiler.program.bundle.spans.toList.idxOf?
      (SpanFacts.rootLocalSpan ⟨2, by decide⟩) = some 603 := by
    rw [show PreparedReflection.actual.compiler.program = PreparedReflection.actual.program by rfl]
    exact SpanFacts.root_local2_span_index
  exact local_span_from_metadata _ _ _ _ _ _ SpanFacts.rootInputBody decl _ 603 body.symm
    (root_body_of_frame frame body identity callee) present rfl spanQuery

open Lean Elab Command in
run_cmd do
  for declaration in #[``actual_root_abi, ``actual_root_load_mir,
      ``root_requires_no_caller_location, ``root_required_target_features, ``root_not_closure_like,
      ``actual_call_hooks_root_abi, ``actual_call_hooks_requires_no_caller_location,
      ``actual_call_hooks_non_capturing_false, ``actual_call_hooks_target_features,
      ``root_abi_entry_flags, ``root_body_entry_flags,
      ``root_return_argument_compat, ``root_slice_argument_compat, ``root_usize_argument_compat,
      ``root_preamble_span, ``root_required_constants, ``root_user_relevance,
      ``relevance_after_push, ``init_root_frame, ``actual_push_raw_root,
      ``root_local4_normalized, ``actual_call_hooks_push_raw, ``root_compute_local4,
      ``root_local0_normalized, ``root_local1_normalized, ``root_local2_normalized,
      ``root_compute_local0, ``root_compute_local1, ``root_compute_local2, ``root_always_live,
      ``actual_push_done_root, ``actual_call_hooks_push_done,
      ``root_local0_span, ``root_local1_span, ``root_local2_span] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"

end DuplicatePrefix.CallEntryFacts
