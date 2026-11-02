import duplicate_prefix.MetadataEntryFacts
namespace DuplicatePrefix.TrackedFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable def raw (callee : CallInstance) (body : LoadedBody) (preamble : SpanRef)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (destination : RuntimeStackPlace Provenance) (cont : ReturnContinuation) (identity : LocalsIdentity) :
    Frame Provenance LocalLayout MachineHooks.FrameExtra :=
  let frame : Frame Provenance LocalLayout Unit := Frame.create body callee () cont destination preamble identity
  {body := frame.body, bodyIdentity := frame.bodyIdentity, functionInstance := frame.functionInstance,
   extra := {borrowTracker := machine.borrowTracker.map (fun _ => {}), catchUnwind := none, userRelevance := 0, dataRace := machine.dataRace.map (fun _ => {})},
   returnContinuation := frame.returnContinuation, returnPlace := frame.returnPlace,
   localsIdentity := frame.localsIdentity, locals := frame.locals, vaList := frame.vaList,
   trackCallerArg := frame.trackCallerArg, location := frame.location}
 theorem user_relevance {K User Extra : Type} (crates : Array Nat)
    (callee : CallInstance) (inlineAttr : CompilerVirtualFacts.inlineAttribute
      PreparedReflection.actual.compiler.lifecycle.frames.calls.scopes callee = .ok none)
    (requires : CompilerRuntimeQueries.requiresCallerLocation
      PreparedReflection.actual.compiler.lifecycle.frames.calls.runtime callee = .ok true)
    (frame : Frame Provenance LocalLayout Extra) (state : MachineHooks.State K User)
    (sameCallee : frame.functionInstance = callee) :
    FrameMetadata.userRelevance (CompilerFrameMetadata.hooks PreparedReflection.actual.compiler.lifecycle.frames crates)
      frame state = .ok 0 state := by
  unfold FrameMetadata.userRelevance
  rw [sameCallee]
  simp only [CompilerFrameMetadata.hooks, inlineAttr]
  unfold_frame_meta
  rw [requires]
  rfl
 theorem init_frame (crates : Array Nat) (callee : CallInstance) (body : LoadedBody) (preamble : SpanRef)
    (inlineAttr : CompilerVirtualFacts.inlineAttribute
      PreparedReflection.actual.compiler.lifecycle.frames.calls.scopes callee = .ok none)
    (requires : CompilerRuntimeQueries.requiresCallerLocation
      PreparedReflection.actual.compiler.lifecycle.frames.calls.runtime callee = .ok true)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (destination : RuntimeStackPlace Provenance) (cont : ReturnContinuation) (identity : LocalsIdentity) :
    MachineHooks.initFrame (FrameMetadata.userRelevance
      (CompilerFrameMetadata.hooks PreparedReflection.actual.compiler.lifecycle.frames crates))
      (Frame.create body callee () cont destination preamble identity) state =
      .ok (raw callee body preamble state.machine destination cont identity) state := by
  unfold MachineHooks.initFrame
  have relevance := user_relevance crates callee inlineAttr requires
    (Frame.create body callee () cont destination preamble identity : Frame Provenance LocalLayout Unit) state rfl
  simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure] at relevance ⊢
  rw [relevance]
  rfl
 theorem relevance_after_push (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K User) (zero : frame.extra.userRelevance = 0)
    (thread : Miri.Concurrency.ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (index : Nat) (cached : thread.topUserRelevantFrame = some index)
    (cachedFrame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (valid : index < frames.size) (lookup : frames[index]? = some cachedFrame)
    (positive : cachedFrame.extra.userRelevance > 0) :
    FrameRelevance.afterStackPush false (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames frame machine) := by
  have frameEq : frames[index]'valid = cachedFrame := (Array.getElem?_eq_some_iff.mp lookup).choose_spec
  have nonzero : cachedFrame.extra.userRelevance ≠ 0 := by
    intro equals
    simpa [equals] using positive
  unfold FrameRelevance.afterStackPush
  unfold_relevance_helpers
  simp [MachineHooks.currentFrame, Storage.withCurrent, Stack.currentFrame?, Array.back?_push,
    zero, active, cached, FrameRelevance.top, Array.getElem?_push_lt valid, lookup,
    frameEq, nonzero,
    bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]
noncomputable def pushed (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (callee : CallInstance) (body : LoadedBody) (preamble : SpanRef)
    (destination : RuntimeStackPlace Provenance) (cont : ReturnContinuation) :=
  let fresh := CallEntryFacts.freshRoot machine
  Storage.withCurrent frames (raw callee body preamble fresh.1 destination cont fresh.2) fresh.1
/-- Internal composition with immutable compiler span/constant queries. -/
 theorem push_raw_of_metadata (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (debug : options.place.debugAssertions = false)
    (callee : CallInstance) (body : LoadedBody) (preamble : SpanRef)
    (inlineAttr : CompilerVirtualFacts.inlineAttribute
      PreparedReflection.actual.compiler.lifecycle.frames.calls.scopes callee = .ok none)
    (requires : CompilerRuntimeQueries.requiresCallerLocation
      PreparedReflection.actual.compiler.lifecycle.frames.calls.runtime callee = .ok true)
    (preambleEq : CompilerLifecycle.preambleSpan PreparedReflection.actual.compiler.lifecycle.lifecycle body =
      (pure preamble : MachineHooks.M MiriMemoryKind Machine.RootUser SpanRef))
    (constantQueries : ∀ (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
      (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
      (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      frame.bodyIdentity = body.identity → frame.functionInstance = callee →
      CompilerLifecycle.requiredConstants PreparedReflection.actual.compiler.lifecycle.lifecycle body
        (Storage.withCurrent frames frame machine) = .ok () (Storage.withCurrent frames frame machine))
    (state : CanonicalConfigFacts.RootState) (destination : RuntimeStackPlace Provenance) (cont : ReturnContinuation)
    (thread : Miri.Concurrency.ThreadRecord) (active : state.machine.threads.activeThread? = some thread)
    (index : Nat) (cached : thread.topUserRelevantFrame = some index)
    (cachedFrame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (valid : index < state.stack.frames.size) (lookup : state.stack.frames[index]? = some cachedFrame)
    (positive : cachedFrame.extra.userRelevance > 0) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).pushRaw ()
      callee body destination cont state =
      .ok () (pushed state.stack.frames state.machine callee body preamble destination cont) := by
  change CallMachine.pushRaw (PreparedContracts.actualConfig options () remaining span).lifecycle
    (PreparedContracts.actualConfig options () remaining span).compiler.debugAssertions callee body destination cont state = _
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  unfold CallMachine.pushRaw
  rw [fields.debug, debug, fields.freshLocalsIdentity, fields.preambleSpan, fields.frameCompiler, fields.requiredConstants]
  simp only [Bool.false_and, Bool.false_eq_true, ite_false, bind, EStateM.bind, get, getThe,
    MonadStateOf.get, EStateM.get, set, MonadStateOf.set, EStateM.set,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  rw [preambleEq]
  dsimp only [pure, EStateM.pure]
  rw [init_frame options.userRelevantCrates callee body preamble inlineAttr requires]
  dsimp only [pure, EStateM.pure]
  let fresh := CallEntryFacts.freshRoot state.machine
  have checks := constantQueries state.stack.frames (raw callee body preamble fresh.1 destination cont fresh.2) fresh.1 rfl rfl
  dsimp only [fresh, CallEntryFacts.freshRoot, Storage.withCurrent] at checks
  rw [checks]
  exact relevance_after_push state.stack.frames (raw callee body preamble fresh.1 destination cont fresh.2)
    fresh.1 rfl thread active index cached cachedFrame valid lookup positive
end DuplicatePrefix.TrackedFrame
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.TrackedFrame." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved tracked-frame dependency {dependency}"
