import empty_function.ProjectedBody
import empty_function.TerminatorStep
import empty_function.FrameExit
namespace EmptyFunction.ProjectedReady
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.Configuration EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

def popped (s : Static) (p : Packet) (tracker : MachineHooks.BorrowState)
    (destination : InputDraft.LocalDestination s p tracker) (older : Array LocalUnit.F)
    (bound : destination.localId < destination.caller.locals.size) (frame previous : LocalUnit.F) (index : Nat) :
    MachineHooks.MachineState MiriMemoryKind RootUser :=
  FrameExit.afterRelevanceAt (older.push (ProjectedModel.caller s p tracker destination bound)) frame
    (TerminatorStep.after (LocalUnit.current (older.push (ProjectedModel.caller s p tracker destination bound)) frame
      (ProjectedModel.initializedMachine s p tracker destination older bound frame previous))).machine index

theorem resources (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    (destination : InputDraft.LocalDestination s p input.tracker) (older : Array LocalUnit.F)
    (bound : destination.localId < destination.caller.locals.size) (frame previous : LocalUnit.F) (index : Nat) :
    let machine := popped s p input.tracker destination older bound frame previous index
    machine.memory = p.before.machine.memory ∧
    machine.user.addresses = p.before.machine.user.addresses ∧
    machine.borrowTracker = some input.tracker ∧ machine.dataRace = none ∧
    machine.user.payload.payload.user.backend = .none ∧
    machine.user.payload.payload.user.runtime.extras.allocations = p.before.machine.user.payload.payload.user.runtime.extras.allocations ∧
    machine.user.payload.payload.user.choices = p.before.machine.user.payload.payload.user.choices ∧
    machine.user.payload.ghost = false ∧ machine.user.payload.validation = .Shallow := by
  have fields := MetadataBinding.fields s metadata capacity
  have tracked := input.world.enabled
  dsimp only
  unfold popped ProjectedModel.initializedMachine FrameExit.afterRelevanceAt FrameExit.afterRelevance
  simp only [TerminatorStep.after,LocalUnit.current]
  unfold FrameRelevance.pushedMachine
  rw [fields.freshLocalsIdentity]
  by_cases pushed : previous.extra.userRelevance ≤ frame.extra.userRelevance <;>
    by_cases popped : index = (older.push (ProjectedModel.caller s p input.tracker destination bound)).size <;>
    simp only [Array.size_push] at popped
  all_goals simp [pushed,popped,TerminatorStep.setControl,EvalConfiguration.identity,runtime.noRace,
      runtime.backend,runtime.ghost,runtime.shallow,tracked]

theorem before_terminator (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (p : Packet) (runtime : RuntimeProfile s p) (tracker : MachineHooks.BorrowState)
    (destination : InputDraft.LocalDestination s p tracker) (older : Array LocalUnit.F)
    (bound : destination.localId < destination.caller.locals.size) (frame previous : LocalUnit.F) :
    let current := LocalUnit.current (older.push (ProjectedModel.caller s p tracker destination bound)) frame
      (ProjectedModel.initializedMachine s p tracker destination older bound frame previous)
    (ExecutionMachine.stepHooks s.cfg s.limits).beforeTerminator () current = (TerminatorStep.after current,.ok ()) := by
  dsimp only
  have fields := MetadataBinding.fields s metadata capacity
  apply TerminatorStep.canonical s metadata capacity
  all_goals unfold ProjectedModel.initializedMachine FrameRelevance.pushedMachine
  all_goals rw [fields.freshLocalsIdentity]
  case fixed => split <;> exact runtime.fixedScheduling
  case gc => split <;> exact runtime.gc
  case unchecked => split <;> exact runtime.unchecked

theorem active (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (p : Packet) (tracker : MachineHooks.BorrowState)
    (destination : InputDraft.LocalDestination s p tracker) (older : Array LocalUnit.F)
    (bound : destination.localId < destination.caller.locals.size) (frame previous : LocalUnit.F)
    (thread : Concurrency.ThreadRecord) (active : p.before.machine.threads.activeThread? = some thread) :
    ∃ current, (ProjectedModel.initializedMachine s p tracker destination older bound frame previous).threads.activeThread? = some current := by
  have fields := MetadataBinding.fields s metadata capacity
  unfold ProjectedModel.initializedMachine FrameRelevance.pushedMachine
  rw [fields.freshLocalsIdentity]
  split
  · refine ⟨{thread with topUserRelevantFrame := some (older.push (ProjectedModel.caller s p tracker destination bound)).size},?_⟩
    change (p.before.machine.threads.threads.mapIdx (fun index old =>
      if index == p.before.machine.threads.activeThread.toNat then
        {old with topUserRelevantFrame := some (older.push (ProjectedModel.caller s p tracker destination bound)).size} else old))[p.before.machine.threads.activeThread.toNat]? = _
    rw [List.getElem?_mapIdx]
    change p.before.machine.threads.threads[p.before.machine.threads.activeThread.toNat]? = some thread at active
    rw [active]
    simp
  · exact ⟨thread,active⟩

end EmptyFunction.ProjectedReady
