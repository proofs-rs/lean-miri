import duplicate_prefix.MetadataCallSummary
namespace DuplicatePrefix.MetadataOutputFacts
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.Concurrency
open MetadataCallSummary MetadataUncachedCall
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem memory_eq (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (valid : 0 < caller.locals.size)
    (current done : CompilerFrameContext.ActualFrame) (thread : ThreadRecord) :
    (outputMachine options remaining span frames caller machine valid current done thread).memory = machine.memory := by
  simp only [outputMachine,PtrMetadataReturn.poppedMachine,GenericPopFrame.afterRelevanceAt]
  split <;> exact MetadataPushFacts.memory_eq options remaining span frames (cachedCaller caller valid) machine current

theorem tracked (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (valid : 0 < caller.locals.size)
    (current done : CompilerFrameContext.ActualFrame) (thread : ThreadRecord)
    (tracker : MachineHooks.BorrowState) (source : machine.borrowTracker = some tracker) :
    (outputMachine options remaining span frames caller machine valid current done thread).borrowTracker = some tracker := by
  simp only [outputMachine,PtrMetadataReturn.poppedMachine,GenericPopFrame.afterRelevanceAt]
  split <;> exact MetadataPushFacts.tracked options remaining span frames (cachedCaller caller valid) machine current tracker source

theorem ghost_eq (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (valid : 0 < caller.locals.size)
    (current done : CompilerFrameContext.ActualFrame) (thread : ThreadRecord) :
    (outputMachine options remaining span frames caller machine valid current done thread).user.payload.ghost = machine.user.payload.ghost := by
  unfold outputMachine
  rw [PtrMetadataReturn.popped_user,PtrMetadataReturn.accounted_ghost]
  exact MetadataPushFacts.ghost_eq options remaining span frames (cachedCaller caller valid) machine current

theorem validation_eq (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (valid : 0 < caller.locals.size)
    (current done : CompilerFrameContext.ActualFrame) (thread : ThreadRecord) :
    (outputMachine options remaining span frames caller machine valid current done thread).user.payload.validation = machine.user.payload.validation := by
  unfold outputMachine
  rw [PtrMetadataReturn.popped_user,PtrMetadataReturn.accounted_validation]
  exact MetadataPushFacts.validation_eq options remaining span frames (cachedCaller caller valid) machine current

theorem unchecked (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (valid : 0 < caller.locals.size)
    (current done : CompilerFrameContext.ActualFrame) (thread : ThreadRecord)
    (source : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false) :
    ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      (outputMachine options remaining span frames caller machine valid current done thread).user).checkedArithmetic = false := by
  have known := MetadataPushFacts.unchecked options remaining span frames (cachedCaller caller valid) machine current source
  unfold outputMachine
  rw [PtrMetadataReturn.popped_user]
  unfold PtrMetadataReturn.accountedMachine SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators] at known ⊢
  exact known

theorem no_gc (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (valid : 0 < caller.locals.size)
    (current done : CompilerFrameContext.ActualFrame) (thread : ThreadRecord)
    (source : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0) :
    ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      (outputMachine options remaining span frames caller machine valid current done thread).user).gcInterval = 0 := by
  have known := MetadataPushFacts.no_gc options remaining span frames (cachedCaller caller valid) machine current source
  unfold outputMachine
  rw [PtrMetadataReturn.popped_user]
  unfold PtrMetadataReturn.accountedMachine SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators] at known ⊢
  exact known

theorem fixed_eq (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (valid : 0 < caller.locals.size)
    (current done : CompilerFrameContext.ActualFrame) (thread : ThreadRecord) :
    (outputMachine options remaining span frames caller machine valid current done thread).threads.fixedScheduling = machine.threads.fixedScheduling := by
  simp only [outputMachine,PtrMetadataReturn.poppedMachine,GenericPopFrame.afterRelevanceAt]
  split <;> exact MetadataPushFacts.fixed_eq options remaining span frames (cachedCaller caller valid) machine current

theorem relevance_active (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState K User) (thread : ThreadRecord)
    (source : machine.threads.activeThread? = some thread) :
    (GenericPopFrame.afterRelevance frames frame machine).threads.activeThread? =
      some {thread with topUserRelevantFrame := FrameRelevance.computeTop ⟨frames.push frame⟩ 1} := by
  have lookup : machine.threads.threads[machine.threads.activeThread.toNat]? = some thread := source
  unfold GenericPopFrame.afterRelevance ThreadManager.activeThread?
  unfold_internal ".ThreadManager.get?"
  simp [List.getElem?_mapIdx,lookup]

theorem active_exists (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (valid : 0 < caller.locals.size)
    (current done : CompilerFrameContext.ActualFrame) (thread : ThreadRecord)
    (source : machine.threads.activeThread? = some thread) :
    ∃ finalThread, (outputMachine options remaining span frames caller machine valid current done thread).threads.activeThread? = some finalThread := by
  have known := MetadataPushFacts.active options remaining span frames (cachedCaller caller valid) machine current thread source
  let helperThread := PushThread.after thread (frames.size+1) (MetadataFrame.rank options.userRelevantCrates) current.extra.userRelevance
  let post := PtrMetadataReturn.accountedMachine options remaining span (MetadataPushFacts.posted options remaining span frames (cachedCaller caller valid) machine current)
  have postActive : post.threads.activeThread? = some helperThread := known
  simp only [outputMachine,PtrMetadataReturn.poppedMachine,GenericPopFrame.afterRelevanceAt]
  split
  · exact ⟨_,relevance_active (frames.push (cachedCaller caller valid)) done post helperThread postActive⟩
  · exact ⟨helperThread,postActive⟩
theorem addresses_eq (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (valid : 0 < caller.locals.size)
    (current done : CompilerFrameContext.ActualFrame) (thread : ThreadRecord) :
    (outputMachine options remaining span frames caller machine valid current done thread).user.addresses = machine.user.addresses := by
  unfold outputMachine
  rw [PtrMetadataReturn.popped_user]
  unfold PtrMetadataReturn.accountedMachine SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  simp only [MetadataPushFacts.posted,MetadataPush.completed,MetadataPushFacts.initial,Storage.withCurrent,GenericPushRelevance.afterPush]
  split <;> unfold MetadataPush.fresh CallEntryFacts.freshRoot PtrMetadataReturn.accountedMachine SourceControl.accounted
  all_goals rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  all_goals rfl

theorem types_eq (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (valid : 0 < caller.locals.size)
    (current done : CompilerFrameContext.ActualFrame) (thread : ThreadRecord) :
    (outputMachine options remaining span frames caller machine valid current done thread).user.payload.payload.user.types = machine.user.payload.payload.user.types := by
  unfold outputMachine
  rw [PtrMetadataReturn.popped_user]
  unfold PtrMetadataReturn.accountedMachine SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  simp only [MetadataPushFacts.posted,MetadataPush.completed,MetadataPushFacts.initial,Storage.withCurrent,GenericPushRelevance.afterPush]
  split <;> unfold MetadataPush.fresh CallEntryFacts.freshRoot PtrMetadataReturn.accountedMachine SourceControl.accounted
  all_goals rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  all_goals rfl

theorem backend_eq (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (valid : 0 < caller.locals.size)
    (current done : CompilerFrameContext.ActualFrame) (thread : ThreadRecord) :
    (outputMachine options remaining span frames caller machine valid current done thread).user.payload.payload.user.backend = machine.user.payload.payload.user.backend := by
  unfold outputMachine
  rw [PtrMetadataReturn.popped_user]
  unfold PtrMetadataReturn.accountedMachine SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  simp only [MetadataPushFacts.posted,MetadataPush.completed,MetadataPushFacts.initial,Storage.withCurrent,GenericPushRelevance.afterPush]
  split <;> unfold MetadataPush.fresh CallEntryFacts.freshRoot PtrMetadataReturn.accountedMachine SourceControl.accounted
  all_goals rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  all_goals rfl

theorem extras_eq (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (valid : 0 < caller.locals.size)
    (current done : CompilerFrameContext.ActualFrame) (thread : ThreadRecord) :
    (outputMachine options remaining span frames caller machine valid current done thread).user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras := by
  unfold outputMachine
  rw [PtrMetadataReturn.popped_user]
  unfold PtrMetadataReturn.accountedMachine SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  simp only [MetadataPushFacts.posted,MetadataPush.completed,MetadataPushFacts.initial,Storage.withCurrent,GenericPushRelevance.afterPush]
  split <;> unfold MetadataPush.fresh CallEntryFacts.freshRoot PtrMetadataReturn.accountedMachine SourceControl.accounted
  all_goals rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  all_goals rfl

end
end DuplicatePrefix.MetadataOutputFacts
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.MetadataOutputFacts." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved metadata return state dependency {dependency}"
