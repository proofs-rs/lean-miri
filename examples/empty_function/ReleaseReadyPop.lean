import empty_function.ReturnStep
import empty_function.FrameExit
import empty_function.ProtectionOutcome
import empty_function.ReleaseLookup
import empty_function.ReleaseNondata
import empty_function.ProjectionSnapshot
namespace EmptyFunction.ReleaseReadyPop
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Specification EmptyFunction.UnitRetag
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
abbrev Machine := ProtectionOutcome.Machine

/-- Actual protector release preserves the projections needed by unit copying.
A live-tree writeback retains its real filter/push memory normalization. -/
theorem release (s : Static) (metadata : Metadata s)
    (frames : Array LocalUnit.F) (frame : LocalUnit.F) (machine : Machine)
    (borrow : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrow)
    (ready : ProtectionOutcome.ReleaseReady machine borrow) :
    ∃ after,
      MachineHooks.beforeStackPopWithEnsure s.cfg.retag.ensureTreeExtra
        (LocalUnit.current frames frame machine) = .ok () (LocalUnit.current frames frame after) ∧
      ProtectionOutcome.Stable machine after ∧ after.user.addresses = machine.user.addresses ∧
      (∀ id, after.memory.getAllocInfo id = machine.memory.getAllocInfo id) ∧
      (∀ id, after.memory.isAllocLive id = machine.memory.isAllocLive id) := by
  cases ready with
  | empty tracker enabled empty =>
    have released := FrameExit.release_empty s.cfg.retag.ensureTreeExtra frames frame machine tracker borrow
      enabled frameBorrow (by rw [empty])
    exact ⟨machine,released,⟨rfl,rfl,rfl,rfl,rfl⟩,rfl,(fun _ => rfl),(fun _ => rfl)⟩
  | nondata tracker id tag info enabled borrowed infoEq kind =>
    let baseFrame := {frame with extra := {frame.extra with borrowTracker := some {}}}
    have rebuilt : registeredFrame baseFrame {} id tag = frame := by
      simp only [registeredFrame,baseFrame,←borrowed,←frameBorrow]
    have released := ReleaseNondata.nondata s.cfg.retag.ensureTreeExtra frames baseFrame machine tracker
      enabled id tag info infoEq kind
    rw [rebuilt] at released
    refine ⟨_,released,⟨rfl,rfl,rfl,rfl,rfl⟩,rfl,(fun _ => rfl),(fun _ => rfl)⟩
  | live tracker id tag entry enabled borrowed live releasedTree =>
    let baseFrame := {frame with extra := {frame.extra with borrowTracker := some {}}}
    have rebuilt : registeredFrame baseFrame {} id tag = frame := by
      simp only [registeredFrame,baseFrame,←borrowed,←frameBorrow]
    obtain ⟨binding,ensure,sync⟩ := ConcreteProtection.bindings s metadata (InitializationPrefix.capacity_positive s)
    have released := ReleaseLookup.live .global (ConcreteProtection.source s).globals sync frames baseFrame
      machine tracker enabled id entry tag live releasedTree
    rw [←ensure,rebuilt] at released
    refine ⟨_,released,⟨rfl,rfl,rfl,rfl,rfl⟩,rfl,?_,?_⟩
    · intro query
      exact ProjectionSnapshot.replace_info machine.memory id entry entry.allocation.extra live query
    · intro query
      exact ProjectionSnapshot.replace_live machine.memory id entry entry.allocation.extra live query

/-- Release, relevance-cache maintenance and the real raw frame pop. The
release certificate is a derived protection post, not a caller condition. -/
theorem pop (s : Static) (metadata : Metadata s)
    (frames : Array LocalUnit.F) (frame : LocalUnit.F) (machine : Machine)
    (borrow : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrow)
    (ready : ProtectionOutcome.ReleaseReady machine borrow)
    (thread : Concurrency.ThreadRecord) (active : machine.threads.activeThread? = some thread) :
    ∃ after,
      (ReturnStep.control s).popFrame () (LocalUnit.current frames frame machine) =
        ((⟨⟨frames⟩,after⟩ : State),.ok frame) ∧
      after.user.addresses = machine.user.addresses ∧
      (∀ id, after.memory.getAllocInfo id = machine.memory.getAllocInfo id) ∧
      (∀ id, after.memory.isAllocLive id = machine.memory.isAllocLive id) ∧
      after.user.payload.ghost = machine.user.payload.ghost ∧
      after.user.payload.validation = machine.user.payload.validation := by
  obtain ⟨releasedMachine,released,stable,addresses,infos,lives⟩ :=
    release s metadata frames frame machine borrow frameBorrow ready
  have activeAfter : releasedMachine.threads.activeThread? = some thread := by rw [stable.threads];exact active
  have relevant := FrameExit.relevance_before_pop frames frame releasedMachine thread activeAfter
  let after := FrameExit.afterRelevanceAt frames frame releasedMachine (thread.topUserRelevantFrame.getD frames.size)
  refine ⟨after,?_,?_,?_,?_,?_,?_⟩
  · change MachineHooks.run (TypedMachineBindings.popRaw
      (TypedMachineBindings.retagHooks s.cfg.access s.cfg.retag)) _ = _
    unfold TypedMachineBindings.popRaw
    simp only [TypedMachineBindings.retagHooks,MachineHooks.run,Call.run,bind,Bind.bind,EStateM.bind]
    rw [released]
    simp only [LocalUnit.current,FrameExit.withCurrent] at relevant ⊢
    rw [relevant]
    simp [LocalUnit.current,FrameExit.withCurrent,after,Stack.popFrame,
      get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,
      set,MonadStateOf.set,EStateM.set,pure,Pure.pure,EStateM.pure,Except.pure]
  · dsimp only [after,FrameExit.afterRelevanceAt,FrameExit.afterRelevance]
    split <;>exact addresses
  · intro query
    dsimp only [after,FrameExit.afterRelevanceAt,FrameExit.afterRelevance]
    split <;>exact infos query
  · intro query
    dsimp only [after,FrameExit.afterRelevanceAt,FrameExit.afterRelevance]
    split <;>exact lives query

  · dsimp only [after,FrameExit.afterRelevanceAt,FrameExit.afterRelevance]
    split <;>exact stable.ghost
  · dsimp only [after,FrameExit.afterRelevanceAt,FrameExit.afterRelevance]
    split <;>exact stable.validation

end EmptyFunction.ReleaseReadyPop
