import empty_function.LocalPreflight
namespace EmptyFunction.LocalInit
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.Concurrency
open EmptyFunction.WholeCall EmptyFunction.Specification EmptyFunction.Configuration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

def cachedState (s : Static) (p : Packet) (tracker : MachineHooks.BorrowState)
    (destination : InputDraft.LocalDestination s p tracker) (older : Array LocalUnit.F)
    (bound : destination.localId < destination.caller.locals.size) : State :=
  LocalUnit.current older (LocalImmediate.cached destination.caller destination.localId destination.slot
    s.abi.ret.layout bound) p.before.machine

theorem push_cached (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p) (capacity : 0 < s.capacity)
    (destination : InputDraft.LocalDestination s p input.tracker)
    (older : Array LocalUnit.F) (original : p.before.stack.frames = older.push destination.caller)
    (bound : destination.localId < destination.caller.locals.size)
    (continuation : ReturnContinuation) :
    ∃ frame machine,
      (ExecutionMachine.callHooks s.cfg s.limits).pushRaw () s.functionInstance s.loaded
        p.destination continuation (cachedState s p input.tracker destination older bound) =
        .ok () (⟨⟨(cachedState s p input.tracker destination older bound).stack.frames.push frame⟩,machine⟩ : State) ∧
      (∃ previous, machine = FrameRelevance.pushedMachine (cachedState s p input.tracker destination older bound).stack.frames frame previous
        (s.cfg.lifecycle.freshLocalsIdentity (cachedState s p input.tracker destination older bound).machine).1) ∧
      frame.extra.borrowTracker = some {} ∧ frame.extra.dataRace = none ∧
      frame.body = s.loaded.body ∧ frame.bodyIdentity = s.loaded.identity ∧
      frame.functionInstance = s.functionInstance ∧ frame.location = .unwinding metadata.preamble ∧
      frame.returnContinuation = continuation ∧ frame.returnPlace = p.destination ∧
      frame.locals = #[{value := .dead,layout := none}] ∧ frame.vaList = #[] ∧
      frame.trackCallerArg = none ∧
      machine.borrowTracker = (cachedState s p input.tracker destination older bound).machine.borrowTracker ∧ machine.dataRace = none := by
  have fields := MetadataBinding.fields s metadata capacity
  obtain ⟨definition, definitionAt⟩ := metadata.frameDefinition
  let frame := EmptyFunction.Init.created s.cfg.lifecycle (cachedState s p input.tracker destination older bound) s.loaded s.functionInstance p.destination
    continuation metadata.preamble s.prepared.compiler.lifecycle.frames s.options.userRelevantCrates definition
  let machine := (s.cfg.lifecycle.freshLocalsIdentity (cachedState s p input.tracker destination older bound).machine).1
  have threads : machine.threads = (cachedState s p input.tracker destination older bound).machine.threads := by
    simp only [machine, fields.freshLocalsIdentity]
  have active : machine.threads.activeThread? = some input.thread := by
    rw [threads]
    exact input.active
  have select : ∃ index old,
      FrameRelevance.top ⟨(cachedState s p input.tracker destination older bound).stack.frames.push frame⟩ input.thread.topUserRelevantFrame = some index ∧
      ((cachedState s p input.tracker destination older bound).stack.frames.push frame)[index]? = some old := by
    cases cache : input.thread.topUserRelevantFrame with
    | none =>
      refine ⟨(cachedState s p input.tracker destination older bound).stack.frames.size,frame,?_,?_⟩
      · simp [FrameRelevance.top,cache]
      · simp
    | some index =>
      have bounded : index < (cachedState s p input.tracker destination older bound).stack.frames.size := by
        have bound := input.relevance index cache
        simpa only [original,cachedState,LocalUnit.current,Array.size_push] using bound
      refine ⟨index,(cachedState s p input.tracker destination older bound).stack.frames[index],?_,?_⟩
      · simp [FrameRelevance.top,cache]
      · rw [Array.getElem?_push, if_neg (Nat.ne_of_lt bounded), Array.getElem?_eq_getElem bounded]
  obtain ⟨index,old,cached,selected⟩ := select
  have pushed := EmptyFunction.Init.push_raw s.cfg.lifecycle (cachedState s p input.tracker destination older bound) s.loaded s.functionInstance p.destination
    continuation metadata.preamble s.prepared.compiler.lifecycle.frames s.options.userRelevantCrates definition
    s.prepared.compiler.lifecycle.lifecycle metadata.loweredBody fields.frameCompiler fields.preambleSpan
    fields.requiredConstants metadata.frameInlineAttribute metadata.frameTrackCaller definitionAt
    metadata.lifecycleBody metadata.bodyContents metadata.lifecycleRow input.thread index active old cached selected
  refine ⟨frame,FrameRelevance.pushedMachine (cachedState s p input.tracker destination older bound).stack.frames frame old machine,?_,⟨old,rfl⟩,?_,?_,?_⟩
  · change CallMachine.pushRaw s.cfg.lifecycle s.cfg.compiler.debugAssertions s.functionInstance s.loaded
      p.destination continuation (cachedState s p input.tracker destination older bound) = _
    rw [fields.debug,profile.debug]
    exact pushed
  · simp only [frame,EmptyFunction.Init.created,CompilerFrameMetadata.resolvedFrame]
    have enabled := input.world.enabled
    simp only [machine,fields.freshLocalsIdentity] at *
    simp [enabled,cachedState,LocalUnit.current]
  · simp [frame,EmptyFunction.Init.created,CompilerFrameMetadata.resolvedFrame, fields.freshLocalsIdentity,cachedState,LocalUnit.current,runtime.noRace]
  · have count : s.loaded.body.locals.size = 1 := by rw [metadata.body]; exact Program.one_local
    simp only [frame,EmptyFunction.Init.created,CompilerFrameMetadata.resolvedFrame,EmptyFunction.Init.raw,Frame.create,count,
      Array.replicate_succ,Array.replicate_zero]
    simp [FrameRelevance.pushedMachine,machine,fields.freshLocalsIdentity,cachedState,LocalUnit.current,runtime.noRace]
    split <;> constructor <;> rfl

def rawCore (s : Static) (destination : RuntimeStackPlace Provenance) (continuation : ReturnContinuation) :
    MachineHooks.M MiriMemoryKind RootUser Unit := do
  let hooks := ExecutionMachine.callHooks s.cfg s.limits
  hooks.pushRaw () s.functionInstance s.loaded destination (CanonicalInit.normalizedContinuation s continuation)
  let frame ← MachineHooks.currentFrame
  let preamble ← match frame.location with
    | .unwinding span => pure span
    | .mir _ => throw (StepError.invalidProgram "raw frame does not have preamble location")
  MachineHooks.setCurrentFrame {frame with trackCallerArg := none}
  CanonicalInit.spanAt (← hooks.localSpan s.loaded.body 0)
  CanonicalInit.spanAt preamble
  hooks.pushDone ()

 theorem core_reduction (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (destination : RuntimeStackPlace Provenance) (continuation : ReturnContinuation) :
    Call.zeroImmediateCore (ExecutionMachine.callHooks s.cfg s.limits) () s.functionInstance s.loaded s.abi
      destination continuation = rawCore s destination continuation := by
  let hooks := ExecutionMachine.callHooks s.cfg s.limits
  have mode : hooks.withRetagMode () .FnEntry (pure ((0,0) : Nat × Nat)) = pure (0,0) := by
    funext state
    exact Init.mode_pure .FnEntry ((0,0) : Nat × Nat) state
  have compatible : hooks.checkArgumentCompat () s.abi.ret s.abi.ret = pure true :=
    CanonicalInit.return_compatibility s metadata capacity
  have after : hooks.afterFrameInit () = pure () := rfl
  change Call.zeroImmediateCore hooks () s.functionInstance s.loaded s.abi destination continuation = _
  unfold Call.zeroImmediateCore rawCore
  simp only [mode,compatible,after,bind_pure_comp,bind_assoc,pure_bind]
  with_unfolding_all rfl

 theorem init_whole (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    {choiceCondition : Prop} (resources : ResourceMargins s p choiceCondition) (destination : InputDraft.LocalDestination s p input.tracker)
    (whole : destination.offset = none) (value : Immediate Provenance)
    (immediate : destination.oldOperand = .immediate value) :
    ∃ (older : Array LocalUnit.F) (bound : destination.localId < destination.caller.locals.size)
      (frame : LocalUnit.F) (machine : MachineHooks.MachineState MiriMemoryKind RootUser),
      p.before.stack.frames = older.push destination.caller ∧
      WholeCall.install s p = .ok () (LocalUnit.current (cachedState s p input.tracker destination older bound).stack.frames frame machine) ∧
      frame.body = s.loaded.body ∧ frame.bodyIdentity = s.loaded.identity ∧
      frame.functionInstance = s.functionInstance ∧ frame.location = .mir ⟨0,0⟩ ∧
      frame.locals = #[{value := .live (.immediate .uninit),layout := none}] ∧
      frame.extra.borrowTracker = some {} ∧ frame.extra.dataRace = none ∧ frame.returnPlace = p.destination ∧
      frame.returnContinuation = CanonicalInit.normalizedContinuation s (.goto (some p.returnBlock) p.unwind) ∧
      frame.vaList = #[] ∧ machine.user.payload.ghost = false ∧ machine.user.payload.validation = .Shallow ∧
      (∃ previous, machine = FrameRelevance.pushedMachine (cachedState s p input.tracker destination older bound).stack.frames
        frame previous (s.cfg.lifecycle.freshLocalsIdentity p.before.machine).1) ∧
      machine.borrowTracker = p.before.machine.borrowTracker := by
  have budget : 64 ≤ resources.budget := by have bound := resources.reserve; unfold work at bound; omega
  have capacity : 0 < s.capacity := by have bound := resources.capacity; omega
  have fields := MetadataBinding.fields s metadata capacity
  obtain ⟨older,original⟩ := Array.back?_eq_some_iff.mp destination.current
  have bound : destination.localId < destination.caller.locals.size := Array.getElem?_eq_some_iff.mp destination.slotAt |>.1
  have sameCaller : destination.caller = input.caller := Option.some.inj (destination.current.symm.trans input.current)
  have noClocks : destination.caller.extra.dataRace = none := by rw [sameCaller]; exact input.callerNoClocks
  have preflight := LocalPreflight.operand s metadata profile capacity p input.tracker destination whole value immediate
    noClocks older original bound
  let continuation : ReturnContinuation := .goto (some p.returnBlock) p.unwind
  have initial := Call.zero_entry_immediate (ExecutionMachine.callHooks s.cfg s.limits) () s.functionInstance
    s.loaded s.abi p.destination continuation p.before (cachedState s p input.tracker destination older bound)
    .uninit s.abi.ret.layout (MetadataBinding.caller_location s metadata capacity)
    (MetadataBinding.instance_abi s metadata capacity) (MetadataBinding.target_features s metadata capacity)
    preflight (MetadataBinding.not_closure s metadata capacity) metadata.notVariadic
    (show (ExecutionMachine.callHooks s.cfg s.limits).sameConvention s.abi s.abi = true from beq_self_eq_true _)
    metadata.noArguments rfl (by rw [metadata.body]; exact Program.no_arguments)
  rw [core_reduction s metadata capacity] at initial
  obtain ⟨frame,machine,push,⟨previous,machineEq⟩,tracked,frameNoClocks,body,identity,function,location,
    returning,returnPlace,locals,varargs,callerArg,machineTracker,machineRace⟩ :=
      push_cached s metadata profile p runtime input capacity destination older original bound
        (CanonicalInit.normalizedContinuation s continuation)
  have cleared : {frame with trackCallerArg := none} = frame := by rw [←callerArg]
  have localQuery := CanonicalInit.local_span s metadata capacity
    (cachedState s p input.tracker destination older bound).stack.frames frame machine identity function body
  have done := CanonicalInit.push_done s metadata capacity
    (cachedState s p input.tracker destination older bound).stack.frames frame machine body locals frameNoClocks
  have result : rawCore s p.destination continuation (cachedState s p input.tracker destination older bound) =
      .ok () (LocalUnit.current (cachedState s p input.tracker destination older bound).stack.frames {frame with
        locals := #[{value := .live (.immediate .uninit),layout := none}],location := .mir .start} machine) := by
    unfold rawCore
    simp only [bind,EStateM.bind]
    rw [push]
    dsimp only
    have currentEq := CanonicalInit.get_current (cachedState s p input.tracker destination older bound).stack.frames frame machine
    simp only [LocalUnit.current] at currentEq
    rw [currentEq]
    simp only [location,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]
    have setEq := CanonicalInit.set_current (cachedState s p input.tracker destination older bound).stack.frames
      frame {frame with trackCallerArg := none} machine
    simp only [LocalUnit.current,location] at setEq
    rw [setEq]
    simp only [←location,cleared]
    simp only [LocalUnit.current] at localQuery done
    rw [localQuery]
    dsimp only
    have spanEq := CanonicalInit.span_current metadata.localSpan
      (cachedState s p input.tracker destination older bound).stack.frames frame machine
    simp only [LocalUnit.current] at spanEq
    rw [spanEq]
    dsimp only
    have restoreEq := CanonicalInit.span_current metadata.preamble
      (cachedState s p input.tracker destination older bound).stack.frames
      {frame with location := .unwinding metadata.localSpan} machine
    simp only [LocalUnit.current] at restoreEq
    rw [restoreEq]
    simp only [←location]
    exact done
  let output : LocalUnit.F := {frame with locals := #[{value := .live (.immediate .uninit),layout := none}],location := .mir .start}
  have ghost : machine.user.payload.ghost = false := by
    simp [machineEq,FrameRelevance.pushedMachine,fields.freshLocalsIdentity,cachedState,LocalUnit.current]
    split <;> change p.before.machine.user.payload.ghost = false
    all_goals exact runtime.ghost
  have shallow : machine.user.payload.validation = .Shallow := by
    simp [machineEq,FrameRelevance.pushedMachine,fields.freshLocalsIdentity,cachedState,LocalUnit.current]
    split <;> change p.before.machine.user.payload.validation = .Shallow
    all_goals exact runtime.shallow
  have shape : machine = FrameRelevance.pushedMachine (cachedState s p input.tracker destination older bound).stack.frames
      output previous (s.cfg.lifecycle.freshLocalsIdentity p.before.machine).1 := by rw [machineEq]; rfl
  refine ⟨older,bound,output,machine,original,initial.trans result,body,identity,function,rfl,rfl,tracked,
    frameNoClocks,returnPlace,returning,varargs,ghost,shallow,⟨previous,shape⟩,machineTracker⟩

end EmptyFunction.LocalInit
