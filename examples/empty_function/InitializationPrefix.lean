import empty_function.CanonicalInit
namespace EmptyFunction.InitializationPrefix
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

/-- The actual configuration factory cannot construct its zero-capacity arm.
This follows from Static.built, independently of any resource admission. -/
theorem capacity_positive (s : Static) : 0 < s.capacity := by
  cases value : s.capacity with
  | zero =>
    have built := s.built
    rw [value] at built
    change (Except.error (.resourceExhaustion "execution callback construction capacity") :
      Except StepError Config) = .ok s.cfg at built
    cases built
  | succ count => omega

/-- Pure ABI/compiler preparation reduces actual memory-destination entry to
its source call sequence. Possible retag failures remain actual failures. -/
theorem memory_core (s : Static) (metadata : Metadata s) (p : Packet)
    (place : MPlaceTy Provenance) (encoding : p.destination = .memory place) :
    install s p = CanonicalInit.rawCore s place (.goto (some p.returnBlock) p.unwind) p.before := by
  unfold install
  rw [encoding,CanonicalInit.memory_core s metadata (capacity_positive s),
    CanonicalInit.core_reduction s metadata (capacity_positive s)]

/-- The only remaining effectful part of memory entry: actual protection,
followed by restoring the preamble and activating local zero. This expression
retains every error and its actual failed state. -/
def protectedTail (s : Static) (place : MPlaceTy Provenance) (preamble : SpanRef) :
    MachineHooks.M MiriMemoryKind Configuration.RootUser Unit := do
  (ExecutionMachine.callHooks s.cfg s.limits).protectArgument () place
  CanonicalInit.spanAt preamble
  (ExecutionMachine.callHooks s.cfg s.limits).pushDone ()

/-- Actual ABI preparation, raw push and span setup are discharged without a
numeric reserve. No success premise is imposed on protection or its suffix. -/
theorem memory_at_protection (s : Static) (metadata : Metadata s) (p : Packet)
    (place : MPlaceTy Provenance) (encoding : p.destination = .memory place)
    (frame : LocalUnit.F) (machine : MachineHooks.MachineState MiriMemoryKind Configuration.RootUser)
    (push : (ExecutionMachine.callHooks s.cfg s.limits).pushRaw () s.functionInstance s.loaded
      p.destination (CanonicalInit.normalizedContinuation s (.goto (some p.returnBlock) p.unwind)) p.before =
      .ok () (LocalUnit.current p.before.stack.frames frame machine))
    (body : frame.body = s.loaded.body) (identity : frame.bodyIdentity = s.loaded.identity)
    (function : frame.functionInstance = s.functionInstance)
    (location : frame.location = .unwinding metadata.preamble) (callerArg : frame.trackCallerArg = none) :
    install s p = protectedTail s place metadata.preamble
      (LocalUnit.current p.before.stack.frames {frame with location := .unwinding metadata.localSpan} machine) := by
  rw [memory_core s metadata p place encoding]
  have cleared : {frame with trackCallerArg := none} = frame := by rw [←callerArg]
  have localQuery := CanonicalInit.local_span s metadata (capacity_positive s)
    p.before.stack.frames frame machine identity function body
  unfold CanonicalInit.rawCore
  simp only [bind,EStateM.bind]
  rw [←encoding,push]
  change (do
    let current ← MachineHooks.currentFrame
    let preamble ← match current.location with
      | .unwinding span => pure span
      | .mir _ => throw (StepError.invalidProgram "raw frame does not have preamble location")
    MachineHooks.setCurrentFrame {current with trackCallerArg := none}
    CanonicalInit.spanAt (← (ExecutionMachine.callHooks s.cfg s.limits).localSpan s.loaded.body 0)
    (ExecutionMachine.callHooks s.cfg s.limits).protectArgument () place
    CanonicalInit.spanAt preamble
    (ExecutionMachine.callHooks s.cfg s.limits).pushDone ())
      (LocalUnit.current p.before.stack.frames frame machine) = _
  simp only [bind,EStateM.bind]
  rw [CanonicalInit.get_current]
  simp only [location,EStateM.bind,pure,Pure.pure,EStateM.pure]
  rw [CanonicalInit.set_current]
  simp only [←location,cleared]
  rw [localQuery]
  dsimp only
  rw [CanonicalInit.span_current]
  rfl

/-- The actual source-created frame at the protection boundary. Every witness
and machine update is derived from the raw current caller and metadata. -/
theorem memory_prefix (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    (destination : InputDraft.MemoryDestination s p input.tracker) :
    ∃ frame machine,
      install s p = protectedTail s destination.place metadata.preamble
        (LocalUnit.current p.before.stack.frames {frame with location := .unwinding metadata.localSpan} machine) ∧
      frame.body = s.loaded.body ∧ frame.bodyIdentity = s.loaded.identity ∧
      frame.functionInstance = s.functionInstance ∧ frame.location = .unwinding metadata.preamble ∧
      frame.locals = #[{value := .dead,layout := none}] ∧
      frame.extra.borrowTracker = some {} ∧ frame.extra.dataRace = none ∧
      frame.returnPlace = p.destination ∧
      frame.returnContinuation = CanonicalInit.normalizedContinuation s (.goto (some p.returnBlock) p.unwind) ∧
      frame.vaList = #[] ∧ frame.trackCallerArg = none ∧
      machine.borrowTracker = some input.tracker ∧ machine.dataRace = none ∧
      machine.user.payload.ghost = false ∧ machine.user.payload.validation = .Shallow ∧
      ∃ previous, machine = FrameRelevance.pushedMachine p.before.stack.frames frame previous
        (s.cfg.lifecycle.freshLocalsIdentity p.before.machine).1 := by
  have positive := capacity_positive s
  obtain ⟨frame,machine,push,previous,tracked,noClocks,body,identity,function,location,
      returning,returnPlace,locals,varargs,callerArg,machineTracker,machineRace⟩ :=
    CanonicalInit.push_actual s metadata profile p runtime input positive
      (CanonicalInit.normalizedContinuation s (.goto (some p.returnBlock) p.unwind))
  have prefixEq := memory_at_protection s metadata p destination.place destination.encoding frame machine push
    body identity function location callerArg
  refine ⟨frame,machine,prefixEq,body,identity,function,location,locals,tracked,noClocks,
    returnPlace,returning,varargs,callerArg,?_,machineRace,?_,?_,previous⟩
  · rw [machineTracker,input.world.enabled]
  · obtain ⟨previous,machineEq⟩ := previous
    simp [machineEq,FrameRelevance.pushedMachine,
      (MetadataBinding.fields s metadata positive).freshLocalsIdentity]
    split <;> change p.before.machine.user.payload.ghost = false
    all_goals exact runtime.ghost
  · obtain ⟨previous,machineEq⟩ := previous
    simp [machineEq,FrameRelevance.pushedMachine,
      (MetadataBinding.fields s metadata positive).freshLocalsIdentity]
    split <;> change p.before.machine.user.payload.validation = .Shallow
    all_goals exact runtime.shallow

end EmptyFunction.InitializationPrefix
