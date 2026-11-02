import empty_function.NondataProtection
import empty_function.ReturnSingleton
namespace EmptyFunction.ReturnNondata
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
 theorem pop (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (frames : Array LocalUnit.F) (frame : LocalUnit.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser) (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (enabled : machine.borrowTracker = some (UnitRetag.allocatedTracker tracker room))
    (formed : TreeRuntimeInput.GlobalFormed tracker.global)
    (p : Packet) (id : AllocId) (registry : NondataProtection.Registry p.before id)
    (memory : machine.memory = p.before.machine.memory)
    (thread : Concurrency.ThreadRecord) (active : machine.threads.activeThread? = some thread) :
    (ReturnStep.control s).popFrame ()
      (LocalUnit.current frames (UnitRetag.registeredFrame frame {} id tracker.global.nextPointerTag)
        (UnitRetag.registeredMachine machine (UnitRetag.allocatedTracker tracker room)
          tracker.global.nextPointerTag)) =
      ((⟨⟨frames⟩,FrameExit.afterRelevanceAt frames
          (UnitRetag.registeredFrame frame {} id tracker.global.nextPointerTag)
          machine
          (thread.topUserRelevantFrame.getD frames.size)⟩ : WholeCall.State),
        .ok (UnitRetag.registeredFrame frame {} id tracker.global.nextPointerTag)) := by
  let protectedFrame := UnitRetag.registeredFrame frame {} id tracker.global.nextPointerTag
  let after := machine
  obtain ⟨info,classification,nondata⟩ := NondataProtection.classification p.before id registry
  have releaseEq := UnitRetag.release_nondata_singleton (K := MiriMemoryKind) (U := RootUser)
    s.cfg.retag.ensureTreeExtra frames frame machine (UnitRetag.allocatedTracker tracker room) enabled
    id tracker.global.nextPointerTag formed.nextNotProtected info (by rw [memory]; exact classification) nondata
  simp only [UnitRetag.withCurrent,LocalUnit.current] at releaseEq
  have activeAfter : after.threads.activeThread? = some thread := active
  have relevant := FrameExit.relevance_before_pop frames protectedFrame after thread activeAfter
  change MachineHooks.run (TypedMachineBindings.popRaw
    (TypedMachineBindings.retagHooks s.cfg.access s.cfg.retag)) _ = _
  unfold TypedMachineBindings.popRaw
  simp only [TypedMachineBindings.retagHooks]
  simp only [MachineHooks.run,Call.run,bind,Bind.bind,EStateM.bind]
  simp only [LocalUnit.current] at *
  rw [releaseEq]
  simp only [LocalUnit.current,FrameExit.withCurrent,protectedFrame,after] at relevant ⊢
  rw [relevant]
  simp [LocalUnit.current,FrameExit.withCurrent,protectedFrame,after,Stack.popFrame,
    get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,
    set,MonadStateOf.set,EStateM.set,pure,Pure.pure,EStateM.pure,Except.pure]

end EmptyFunction.ReturnNondata
