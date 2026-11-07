import empty_function.CanonicalInit
namespace EmptyFunction.MemoryInitFinish
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

/-- Internal composition edge: the protection equation is derived by each
raw-input adapter. This lemma is not an initial-state safety contract. -/
theorem finish (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (p : Packet) (destination : MPlaceTy Provenance) (encoding : p.destination = .memory destination)
    (frame : LocalUnit.F) (machine changed : MachineHooks.MachineState MiriMemoryKind EmptyFunction.Configuration.RootUser)
    (borrow : FrameState)
    (push : (ExecutionMachine.callHooks s.cfg s.limits).pushRaw () s.functionInstance s.loaded
      p.destination (CanonicalInit.normalizedContinuation s (.goto (some p.returnBlock) p.unwind)) p.before =
      .ok () (LocalUnit.current p.before.stack.frames frame machine))
    (body : Meaning.FrameMatches frame s.loaded) (identity : frame.bodyIdentity = s.loaded.identity)
    (function : frame.functionInstance = s.functionInstance)
    (location : frame.location = .unwinding metadata.preamble)
    (locals : frame.locals = #[{value := .dead,layout := none}])
    (noClocks : frame.extra.dataRace = none) (callerArg : frame.trackCallerArg = none)
    (protection : TypedRetag.protectInPlaceFunctionArgument s.cfg.retag s.limits.retag destination
      (LocalUnit.current p.before.stack.frames {frame with location := .unwinding metadata.localSpan} machine) =
      .ok () (LocalUnit.current p.before.stack.frames
        {frame with location := .unwinding metadata.localSpan, extra := {frame.extra with borrowTracker := some borrow}} changed)) :
    WholeCall.install s p = .ok ()
      (LocalUnit.current p.before.stack.frames
        {frame with locals := #[{value := .live (.immediate .uninit),layout := none}], location := .mir .start,extra := {frame.extra with borrowTracker := some borrow}} changed) := by
  let continuation : ReturnContinuation := .goto (some p.returnBlock) p.unwind
  let decorated := {frame with extra := {frame.extra with borrowTracker := some borrow}}
  have cleared : {frame with trackCallerArg := none} = frame := by rw [←callerArg]
  have localQuery := CanonicalInit.local_span s metadata capacity p.before.stack.frames frame machine identity function body
  have done := CanonicalInit.push_done s metadata capacity p.before.stack.frames decorated changed body locals noClocks
  have restored : {({frame with location := .unwinding metadata.localSpan, extra := {frame.extra with borrowTracker := some borrow}} : LocalUnit.F) with
      location := .unwinding metadata.preamble} = decorated := by
    unfold decorated
    rw [←location]
  have result : CanonicalInit.rawCore s destination continuation p.before = .ok ()
      (LocalUnit.current p.before.stack.frames {decorated with locals := #[{value := .live (.immediate .uninit),layout := none}], location := .mir .start} changed) := by
    unfold CanonicalInit.rawCore
    simp only [bind,EStateM.bind]
    rw [←encoding,push]
    change (do
      let current ← MachineHooks.currentFrame
      let preamble ← match current.location with
        | .unwinding span => pure span
        | .mir _ => throw (StepError.invalidProgram "raw frame does not have preamble location")
      MachineHooks.setCurrentFrame {current with trackCallerArg := none}
      CanonicalInit.spanAt (← (ExecutionMachine.callHooks s.cfg s.limits).localSpan s.loaded.identity 0)
      (ExecutionMachine.callHooks s.cfg s.limits).protectArgument () destination
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
    dsimp only
    have source : (ExecutionMachine.callHooks s.cfg s.limits).protectArgument () destination =
        TypedRetag.protectInPlaceFunctionArgument s.cfg.retag s.limits.retag destination := rfl
    rw [source,protection]
    dsimp only
    rw [CanonicalInit.span_current]
    dsimp only
    rw [restored]
    exact done
  unfold WholeCall.install
  rw [encoding,CanonicalInit.memory_core s metadata capacity,CanonicalInit.core_reduction s metadata capacity]
  exact result
end EmptyFunction.MemoryInitFinish
