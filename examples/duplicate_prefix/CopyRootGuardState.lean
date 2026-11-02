import duplicate_prefix.CopyRootGuardEntry
import duplicate_prefix.PushThread
namespace DuplicatePrefix.CopyRootGuardState
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
 theorem language_push_fields (options : EvalConfigurationCore.Options)
    (state : CanonicalConfigFacts.RootState) (destination : RuntimeStackPlace Provenance)
    (current : CompilerFrameContext.ActualFrame) :
    let next := LanguageZeroEntry.pushedMachine options state destination current
    next.memory = state.machine.memory ∧ next.borrowTracker = state.machine.borrowTracker ∧
    next.dataRace = state.machine.dataRace ∧ next.user.addresses = state.machine.user.addresses ∧
    next.user.payload.ghost = state.machine.user.payload.ghost ∧
    next.user.payload.validation = state.machine.user.payload.validation ∧
    next.user.payload.payload.user.backend = state.machine.user.payload.payload.user.backend ∧
    next.user.payload.payload.user.runtime.extras = state.machine.user.payload.payload.user.runtime.extras ∧
    next.user.payload.payload.user.types = state.machine.user.payload.payload.user.types ∧
    next.threads.fixedScheduling = state.machine.threads.fixedScheduling := by
  dsimp only [LanguageZeroEntry.pushedMachine,LanguageZeroEntryFacts.completed,Storage.withCurrent]
  unfold GenericPushRelevance.afterPush
  split <;> simp only [CallEntryFacts.freshRoot,CallEntryFacts.cacheTop] <;> repeat' constructor
 theorem language_push_active (options : EvalConfigurationCore.Options)
    (state : CanonicalConfigFacts.RootState) (destination : RuntimeStackPlace Provenance)
    (current : CompilerFrameContext.ActualFrame)
    (thread : Miri.Concurrency.ThreadRecord) (active : state.machine.threads.activeThread? = some thread) :
    ∃ result, (LanguageZeroEntry.pushedMachine options state destination current).threads.activeThread? = some result := by
  let fresh := CallEntryFacts.freshRoot state.machine
  let frame := LanguageZeroEntryFacts.rawFrame options.userRelevantCrates fresh.1 destination fresh.2
  exact ⟨PushThread.after thread state.stack.frames.size frame.extra.userRelevance current.extra.userRelevance,
    PushThread.active_after fresh.1 thread state.stack.frames.size frame.extra.userRelevance current.extra.userRelevance active⟩
 theorem language_frame_borrow (options : EvalConfigurationCore.Options)
    (state : CanonicalConfigFacts.RootState) (destination : RuntimeStackPlace Provenance)
    (tracker : MachineHooks.BorrowState) (tracked : state.machine.borrowTracker = some tracker) :
    (LanguageZeroInstalled.frame options state destination).extra.borrowTracker = some ({} : FrameState) := by
  simp only [LanguageZeroInstalled.frame,LanguageZeroDone.doneFrame,LanguageZeroDone.liveSlot,CallEntryFacts.liveSlot,
    LanguageZeroEntry.rawFrame,LanguageZeroEntryFacts.rawFrame,CallEntryFacts.freshRoot,tracked,Option.map_some]
 theorem language_frame_clocks (options : EvalConfigurationCore.Options)
    (state : CanonicalConfigFacts.RootState) (destination : RuntimeStackPlace Provenance)
    (race : state.machine.dataRace = none) :
    (LanguageZeroInstalled.frame options state destination).extra.dataRace = none := by
  simp only [LanguageZeroInstalled.frame,LanguageZeroDone.doneFrame,LanguageZeroDone.liveSlot,CallEntryFacts.liveSlot,
    LanguageZeroEntry.rawFrame,LanguageZeroEntryFacts.rawFrame,CallEntryFacts.freshRoot,race,Option.map_none]
 theorem language_push_control (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (state : CanonicalConfigFacts.RootState)
    (destination : RuntimeStackPlace Provenance) (current : CompilerFrameContext.ActualFrame) :
    let h := (PreparedContracts.actualConfig options () (remaining+1) span).terminators
    h.getControl (LanguageZeroEntry.pushedMachine options state destination current).user =
      h.getControl state.machine.user := by
  dsimp only
  unfold LanguageZeroEntry.pushedMachine LanguageZeroEntryFacts.completed
  dsimp only [Storage.withCurrent]
  unfold GenericPushRelevance.afterPush
  split <;> rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators] <;> rfl
 theorem accounted_fields (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :
    let next := LanguageZeroStep.accountedMachine options remaining span machine
    next.memory = machine.memory ∧ next.borrowTracker = machine.borrowTracker ∧
    next.threads = machine.threads ∧ next.dataRace = machine.dataRace ∧
    next.user.addresses = machine.user.addresses ∧
    next.user.payload.ghost = machine.user.payload.ghost ∧
    next.user.payload.validation = machine.user.payload.validation ∧
    next.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
    next.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
    next.user.payload.payload.user.types = machine.user.payload.payload.user.types := by
  unfold LanguageZeroStep.accountedMachine PtrMetadataReturn.accountedMachine SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  repeat' constructor
#print axioms language_push_control
#print axioms accounted_fields
#print axioms language_push_fields
#print axioms language_push_active
#print axioms language_frame_borrow
#print axioms language_frame_clocks
end DuplicatePrefix.CopyRootGuardState
