import duplicate_prefix.LenEntryShape
import duplicate_prefix.PtrMetadataReturn
import duplicate_prefix.PushThread
namespace DuplicatePrefix.LenPushFacts
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.Concurrency
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def initial (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :=
  Storage.withCurrent frames caller (PtrMetadataReturn.accountedMachine options remaining span machine)

def destination (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame) :=
  (LocalPlaces.localRuntimePlace frames.size caller 11 RootCompilerFacts.usizeLayout).stackView

def posted (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (current : CompilerFrameContext.ActualFrame) :=
  (LenPush.completed options.userRelevantCrates (initial options remaining span frames caller machine)
    (destination frames caller) current).machine

theorem active (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (current : CompilerFrameContext.ActualFrame)
    (thread : ThreadRecord) (isActive : machine.threads.activeThread? = some thread) :
    (posted options remaining span frames caller machine current).threads.activeThread? =
      some (PushThread.after thread (frames.size+1) (LenFrame.rank options.userRelevantCrates) current.extra.userRelevance) := by
  have freshActive : (LenPush.fresh (initial options remaining span frames caller machine).machine).1.threads.activeThread? = some thread := isActive
  simpa only [posted,LenPush.completed,initial,Storage.withCurrent,LenFrame.rawFrame,
    destination,Frame.create,Array.size_push] using
    PushThread.active_after (LenPush.fresh (initial options remaining span frames caller machine).machine).1
      thread (frames.size+1) (LenFrame.rank options.userRelevantCrates) current.extra.userRelevance freshActive

theorem tracked (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (current : CompilerFrameContext.ActualFrame)
    (tracker : MachineHooks.BorrowState) (isTracked : machine.borrowTracker = some tracker) :
    (posted options remaining span frames caller machine current).borrowTracker = some tracker := by
  simp only [posted,LenPush.completed,initial,Storage.withCurrent,GenericPushRelevance.afterPush,
    LenPush.fresh,CallEntryFacts.freshRoot]
  split <;> exact isTracked

theorem unchecked (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (current : CompilerFrameContext.ActualFrame)
    (source : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false) :
    ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      (posted options remaining span frames caller machine current).user).checkedArithmetic = false := by
  simp only [posted,LenPush.completed,initial,Storage.withCurrent,GenericPushRelevance.afterPush]
  split <;> unfold LenPush.fresh CallEntryFacts.freshRoot PtrMetadataReturn.accountedMachine SourceControl.accounted
  all_goals rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  all_goals rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators] at source
  all_goals exact source
theorem no_gc (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (current : CompilerFrameContext.ActualFrame)
    (source : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0) :
    ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      (posted options remaining span frames caller machine current).user).gcInterval = 0 := by
  simp only [posted,LenPush.completed,initial,Storage.withCurrent,GenericPushRelevance.afterPush]
  split <;> unfold LenPush.fresh CallEntryFacts.freshRoot PtrMetadataReturn.accountedMachine SourceControl.accounted
  all_goals rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  all_goals rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators] at source
  all_goals exact source
theorem ghost_eq (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (current : CompilerFrameContext.ActualFrame) :
    (posted options remaining span frames caller machine current).user.payload.ghost = machine.user.payload.ghost := by
  simp only [posted,LenPush.completed,initial,Storage.withCurrent,GenericPushRelevance.afterPush]
  split <;> unfold LenPush.fresh CallEntryFacts.freshRoot PtrMetadataReturn.accountedMachine SourceControl.accounted
  all_goals rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  all_goals rfl

theorem validation_eq (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (current : CompilerFrameContext.ActualFrame) :
    (posted options remaining span frames caller machine current).user.payload.validation = machine.user.payload.validation := by
  simp only [posted,LenPush.completed,initial,Storage.withCurrent,GenericPushRelevance.afterPush]
  split <;> unfold LenPush.fresh CallEntryFacts.freshRoot PtrMetadataReturn.accountedMachine SourceControl.accounted
  all_goals rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  all_goals rfl

theorem fixed_eq (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (current : CompilerFrameContext.ActualFrame) :
    (posted options remaining span frames caller machine current).threads.fixedScheduling = machine.threads.fixedScheduling := by
  simp only [posted,LenPush.completed,initial,Storage.withCurrent,GenericPushRelevance.afterPush]
  split <;> rfl

theorem memory_eq (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (current : CompilerFrameContext.ActualFrame) :
    (posted options remaining span frames caller machine current).memory = machine.memory := by
  simp only [posted,LenPush.completed,initial,Storage.withCurrent,GenericPushRelevance.afterPush]
  split <;> rfl

theorem addresses_eq (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (current : CompilerFrameContext.ActualFrame) :
    (posted options remaining span frames caller machine current).user.addresses = machine.user.addresses := by
  simp only [posted,LenPush.completed,initial,Storage.withCurrent,GenericPushRelevance.afterPush]
  split <;> unfold LenPush.fresh CallEntryFacts.freshRoot PtrMetadataReturn.accountedMachine SourceControl.accounted
  all_goals rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  all_goals rfl

theorem types_eq (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (current : CompilerFrameContext.ActualFrame) :
    (posted options remaining span frames caller machine current).user.payload.payload.user.types = machine.user.payload.payload.user.types := by
  simp only [posted,LenPush.completed,initial,Storage.withCurrent,GenericPushRelevance.afterPush]
  split <;> unfold LenPush.fresh CallEntryFacts.freshRoot PtrMetadataReturn.accountedMachine SourceControl.accounted
  all_goals rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  all_goals rfl

theorem backend_eq (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (current : CompilerFrameContext.ActualFrame) :
    (posted options remaining span frames caller machine current).user.payload.payload.user.backend = machine.user.payload.payload.user.backend := by
  simp only [posted,LenPush.completed,initial,Storage.withCurrent,GenericPushRelevance.afterPush]
  split <;> unfold LenPush.fresh CallEntryFacts.freshRoot PtrMetadataReturn.accountedMachine SourceControl.accounted
  all_goals rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  all_goals rfl

theorem race_eq (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (current : CompilerFrameContext.ActualFrame) :
    (posted options remaining span frames caller machine current).dataRace = machine.dataRace := by
  simp only [posted,LenPush.completed,initial,Storage.withCurrent,GenericPushRelevance.afterPush]
  split <;> rfl

theorem extras_eq (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (current : CompilerFrameContext.ActualFrame) :
    (posted options remaining span frames caller machine current).user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras := by
  simp only [posted,LenPush.completed,initial,Storage.withCurrent,GenericPushRelevance.afterPush]
  split <;> unfold LenPush.fresh CallEntryFacts.freshRoot PtrMetadataReturn.accountedMachine SourceControl.accounted
  all_goals rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  all_goals rfl

end
end DuplicatePrefix.LenPushFacts
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.LenPushFacts." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved metadata push state dependency {dependency}"
