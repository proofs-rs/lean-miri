import duplicate_prefix.StackPopRelease
import duplicate_prefix.PrimitiveCallReturn
namespace DuplicatePrefix.ActualPopPlan
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def released (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (memory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState) :=
  {machine with memory := memory, borrowTracker := some {tracker with global := tracker.global.endCall borrowFrame}}

theorem pop_of_plan
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState)
    (tracked : machine.borrowTracker = some tracker)
    (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (finalMemory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (plan : StackPopRelease.Plan tracker.global.protectedTags borrowFrame.protectedTags.toList machine.memory finalMemory)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread) :
    let config := PreparedContracts.actualConfig options () remaining span
    (GenericCallReturn.sourceControl config limits).popFrame () (Storage.withCurrent frames frame machine) =
      (⟨⟨frames⟩, GenericPopFrame.afterRelevanceAt frames frame (released machine finalMemory tracker borrowFrame)
        (thread.topUserRelevantFrame.getD frames.size)⟩,.ok frame) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let post := released machine finalMemory tracker borrowFrame
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨pointers, table, globals, choice, retag, width, resolve, ensure, sync⟩ := fields.retagConstruction
  have ensureField : config.retag.ensureTreeExtra = GlobalAllocationMachine.ensure .global globals := by
    rw [retag]
    change pointers.ensureTreeExtra = _
    exact ensure
  have release := StackPopRelease.before_stack_pop_of_plan .global globals sync
    (Storage.withCurrent frames frame machine) tracker frame borrowFrame tracked
    (by simp [Storage.withCurrent,Stack.currentFrame?]) frameTracked finalMemory plan
  have release' : MachineHooks.beforeStackPopWithEnsure
      (TypedMachineBindings.retagHooks config.access config.retag).ensureTreeExtra
      (Storage.withCurrent frames frame machine) = .ok () (Storage.withCurrent frames frame post) := by
    change MachineHooks.beforeStackPopWithEnsure config.retag.ensureTreeExtra _ = _
    rw [ensureField]
    exact release
  change MachineHooks.run (TypedMachineBindings.popRaw (TypedMachineBindings.retagHooks config.access config.retag)) _ = _
  unfold MachineHooks.run Call.run
  rw [GenericPopFrame.pop_after_release_at (TypedMachineBindings.retagHooks config.access config.retag)
    frames frame machine post thread _ release' active (GenericPopFrame.top_nonempty frames frame thread.topUserRelevantFrame)]

theorem pop_single_nonlive
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState)
    (tracked : machine.borrowTracker = some tracker) (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (id : AllocId) (tag : BorTag) (info : AllocationInfo)
    (owned : borrowFrame.protectedTags = #[(id,tag)])
    (lookup : machine.memory.getAllocInfo id = .ok info) (notLive : info.kind ≠ .liveData)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread) :
    let config := PreparedContracts.actualConfig options () remaining span
    (GenericCallReturn.sourceControl config limits).popFrame () (Storage.withCurrent frames frame machine) =
      (⟨⟨frames⟩, GenericPopFrame.afterRelevanceAt frames frame (released machine machine.memory tracker borrowFrame)
        (thread.topUserRelevantFrame.getD frames.size)⟩,.ok frame) := by
  apply pop_of_plan options limits remaining span frames frame machine tracker borrowFrame tracked frameTracked machine.memory _ thread active
  rw [owned]
  exact StackPopRelease.plan_single_nonlive tracker.global.protectedTags machine.memory id tag info lookup notLive

#print axioms pop_of_plan
open Lean Elab Command in
run_cmd do
  for declaration in [``pop_of_plan, ``pop_single_nonlive] do
   for dependency in (← collectAxioms declaration) do
     unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
       throwError "unapproved axiom {dependency}"
end DuplicatePrefix.ActualPopPlan
