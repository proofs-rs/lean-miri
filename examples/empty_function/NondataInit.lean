import empty_function.NondataProtection
namespace EmptyFunction.NondataInit
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

def initializedMachine (s : Static) (p : Packet) (frame previous : LocalUnit.F)
    (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615)
 :=
  NondataProtection.protectedMachine
    (FrameRelevance.pushedMachine p.before.stack.frames frame previous
      (s.cfg.lifecycle.freshLocalsIdentity p.before.machine).1) tracker room

 theorem init_live (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    (resources : ResourceMargins s p)
    (destination : InputDraft.MemoryDestination s p input.tracker)
    (id : AllocId) (tag : BorTag)
    (encoding : destination.place.mplace.ptr.provenance = some (.concrete id tag))
    (registry : NondataProtection.Registry p.before id) :
    ∃ frame machine,
      WholeCall.install s p = .ok () (LocalUnit.current p.before.stack.frames frame machine) ∧
      Meaning.FrameMatches frame s.loaded ∧ frame.bodyIdentity = s.loaded.identity ∧
      frame.functionInstance = s.functionInstance ∧ frame.location = .mir ⟨0,0⟩ ∧
      frame.locals = #[{value := .live (.immediate .uninit),layout := none}] ∧
      frame.extra.borrowTracker = some {protectedTags := #[(id,input.tracker.global.nextPointerTag)]} ∧
      frame.extra.dataRace = none ∧ frame.returnPlace = p.destination ∧
      frame.returnContinuation = CanonicalInit.normalizedContinuation s (.goto (some p.returnBlock) p.unwind) ∧
      frame.vaList = #[] ∧ machine.user.payload.ghost = false ∧ machine.user.payload.validation = .Shallow ∧
      (∃ previous, machine = initializedMachine s p frame previous input.tracker
        (ConcreteProtection.tag_room s p input resources)) := by
  have budget : 64 ≤ resources.budget := by have bound := resources.reserve; unfold work at bound; omega
  have capacity : 0 < s.capacity := by have bound := resources.capacity; omega
  have fields := MetadataBinding.fields s metadata capacity
  let room := ConcreteProtection.tag_room s p input resources
  let continuation : ReturnContinuation := .goto (some p.returnBlock) p.unwind
  obtain ⟨frame,machine,push,⟨previous,machineEq⟩,tracked,noClocks,body,identity,function,location,
    returning,returnPlace,locals,varargs,callerArg,machineTracker,machineRace⟩ :=
      CanonicalInit.push_actual s metadata profile p runtime input capacity
        (CanonicalInit.normalizedContinuation s continuation)
  have pushMemory := push
  rw [destination.encoding] at pushMemory
  have cleared : {frame with trackCallerArg := none} = frame := by rw [←callerArg]
  have localQuery := CanonicalInit.local_span s metadata capacity p.before.stack.frames frame machine identity function body
  have enabled : machine.borrowTracker = some input.tracker := machineTracker.trans input.world.enabled
  have memoryEq : machine.memory = p.before.machine.memory := by
    rw [machineEq]
    unfold FrameRelevance.pushedMachine
    rw [fields.freshLocalsIdentity]
    split <;> rfl
  have addressesEq : machine.user.addresses = p.before.machine.user.addresses := by
    rw [machineEq]
    unfold FrameRelevance.pushedMachine
    rw [fields.freshLocalsIdentity]
    split <;> rfl
  have protect := NondataProtection.protect s metadata capacity p input resources
    destination id tag encoding registry {frame with location := .unwinding metadata.localSpan} machine
    enabled tracked memoryEq addressesEq
  let registered := UnitRetag.registeredFrame frame {} id input.tracker.global.nextPointerTag
  let changed := NondataProtection.protectedMachine machine input.tracker room
  have done := CanonicalInit.push_done s metadata capacity p.before.stack.frames registered changed body locals noClocks
  have restored : {UnitRetag.registeredFrame {frame with location := .unwinding metadata.localSpan}
      {} id input.tracker.global.nextPointerTag with location := .unwinding metadata.preamble} = registered := by
    unfold registered UnitRetag.registeredFrame
    rw [←location]
  have result : CanonicalInit.rawCore s destination.place continuation p.before =
      .ok () (LocalUnit.current p.before.stack.frames {registered with
        locals := #[{value := .live (.immediate .uninit),layout := none}],location := .mir .start} changed) := by
    unfold CanonicalInit.rawCore
    simp only [bind,EStateM.bind]
    rw [pushMemory]
    change (do
      let current ← MachineHooks.currentFrame
      let preamble ← match current.location with
        | .unwinding span => pure span
        | .mir _ => throw (StepError.invalidProgram "raw frame does not have preamble location")
      MachineHooks.setCurrentFrame {current with trackCallerArg := none}
      CanonicalInit.spanAt (← (ExecutionMachine.callHooks s.cfg s.limits).localSpan s.loaded.identity 0)
      (ExecutionMachine.callHooks s.cfg s.limits).protectArgument () destination.place
      CanonicalInit.spanAt preamble
      (ExecutionMachine.callHooks s.cfg s.limits).pushDone ())
      (LocalUnit.current p.before.stack.frames frame machine) = _
    simp only [bind,EStateM.bind]
    rw [CanonicalInit.get_current]
    simp only [location,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]
    rw [CanonicalInit.set_current]
    simp only [←location,cleared]
    rw [localQuery]
    dsimp only
    rw [CanonicalInit.span_current]
    dsimp only
    have protectSource : (ExecutionMachine.callHooks s.cfg s.limits).protectArgument () destination.place =
        TypedRetag.protectInPlaceFunctionArgument s.cfg.retag s.limits.retag destination.place := rfl
    rw [protectSource,protect]
    dsimp only
    rw [CanonicalInit.span_current]
    dsimp only
    rw [restored]
    exact done
  let output : LocalUnit.F := {registered with
    locals := #[{value := .live (.immediate .uninit),layout := none}]
    location := FrameLocation.mir Location.start}
  have ghost : changed.user.payload.ghost = false := by
    simp [changed,NondataProtection.protectedMachine,UnitRetag.registeredMachine,
      UnitRetag.allocatedMachine,machineEq,FrameRelevance.pushedMachine,fields.freshLocalsIdentity]
    split <;> change p.before.machine.user.payload.ghost = false
    all_goals exact runtime.ghost
  have shallow : changed.user.payload.validation = .Shallow := by
    simp [changed,NondataProtection.protectedMachine,UnitRetag.registeredMachine,
      UnitRetag.allocatedMachine,machineEq,FrameRelevance.pushedMachine,fields.freshLocalsIdentity]
    split <;> change p.before.machine.user.payload.validation = .Shallow
    all_goals exact runtime.shallow
  have shape : changed = initializedMachine s p output previous input.tracker room := by
    dsimp only [initializedMachine,changed]
    rw [machineEq]
    rfl
  refine ⟨output,changed,?_,body,identity,function,rfl,rfl,rfl,noClocks,returnPlace,returning,varargs,
    ghost,shallow,⟨previous,shape⟩⟩
  unfold WholeCall.install
  rw [destination.encoding,CanonicalInit.memory_core s metadata capacity,CanonicalInit.core_reduction s metadata capacity]
  exact result
end EmptyFunction.NondataInit
