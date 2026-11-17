import duplicate_prefix.AsMutPtrReturn
import duplicate_prefix.RootThreadCache

namespace DuplicatePrefix.GenericAsMutReturnState
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

noncomputable def machine (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller done : CompilerFrameContext.ActualFrame)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (memory : MemoryState Provenance BorrowTree MiriMemoryKind) (tracker : MachineHooks.BorrowState)
    (borrowFrame : FrameState) (thread : ThreadRecord) :=
  AsMutPtrReturn.poppedMachine frames caller done
    (ActualPopPlan.released (AsMutPtrReturn.accountedMachine options remaining span before) memory tracker borrowFrame)
    (thread.topUserRelevantFrame.getD (frames.push caller).size)

theorem fields (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller done : CompilerFrameContext.ActualFrame)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (memory : MemoryState Provenance BorrowTree MiriMemoryKind) (tracker : MachineHooks.BorrowState)
    (borrowFrame : FrameState) (thread : ThreadRecord) :
    let after := machine options remaining span frames caller done before memory tracker borrowFrame thread
    after.memory = memory ∧ after.borrowTracker = some {tracker with global := tracker.global.endCall borrowFrame} ∧
    after.dataRace = before.dataRace ∧ after.threads.fixedScheduling = before.threads.fixedScheduling ∧
    after.user.addresses = before.user.addresses ∧ after.user.payload.ghost = before.user.payload.ghost ∧
    after.user.payload.validation = before.user.payload.validation ∧
    after.user.payload.payload.user.types = before.user.payload.payload.user.types ∧
    after.user.payload.payload.user.backend = before.user.payload.payload.user.backend ∧
    after.user.payload.payload.user.runtime.extras = before.user.payload.payload.user.runtime.extras := by
  unfold machine AsMutPtrReturn.poppedMachine GenericPopFrame.afterRelevanceAt
  split <;> unfold ActualPopPlan.released AsMutPtrReturn.accountedMachine SourceControl.accounted
  all_goals rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  all_goals exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem control (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller done : CompilerFrameContext.ActualFrame)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (memory : MemoryState Provenance BorrowTree MiriMemoryKind) (tracker : MachineHooks.BorrowState)
    (borrowFrame : FrameState) (thread : ThreadRecord) :
    let hooks := (PreparedContracts.actualConfig options () (remaining+1) span).terminators
    hooks.getControl (machine options remaining span frames caller done before memory tracker borrowFrame thread).user =
      TerminatorClock.advance (hooks.getControl before.user) := by
  unfold machine AsMutPtrReturn.poppedMachine GenericPopFrame.afterRelevanceAt
  split <;> unfold ActualPopPlan.released AsMutPtrReturn.accountedMachine SourceControl.accounted
  all_goals rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  all_goals rfl

/-- The actual helper-pop cache restores the root thread, regardless of whether
as_mut_ptr temporarily became the highest-relevance frame. -/
theorem active (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (caller done : CompilerFrameContext.ActualFrame) (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (memory : MemoryState Provenance BorrowTree MiriMemoryKind) (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState)
    (thread : ThreadRecord) (newRank oldRank : UInt8)
    (enabled : before.threads.activeThread? = some (PushThread.after thread 1 newRank oldRank))
    (cached : thread.topUserRelevantFrame = some 0) :
    (machine options remaining span #[] caller done before memory tracker borrowFrame (PushThread.after thread 1 newRank oldRank)).threads.activeThread? = some thread := by
  exact RootThreadCache.pop_active _ caller done thread newRank oldRank enabled cached

end DuplicatePrefix.GenericAsMutReturnState
open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.GenericAsMutReturnState.fields,``DuplicatePrefix.GenericAsMutReturnState.control,``DuplicatePrefix.GenericAsMutReturnState.active] do
    for dependency in (←collectAxioms declaration) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved generic asmut post-pop state dependency {dependency}"
