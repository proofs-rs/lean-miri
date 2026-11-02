import duplicate_prefix.LenReleaseReturn
import duplicate_prefix.MetadataOutputFacts
namespace DuplicatePrefix.EmptyForestLenReturnState
noncomputable section
open Miri Miri.Input Miri.ABI Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.Concurrency
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def finalMachine (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (tracker : MachineHooks.BorrowState)
    (borrowFrame : FrameState)
    (releasedMemory : MemoryState Provenance BorrowTree MiriMemoryKind) (thread : ThreadRecord) :=
  PtrMetadataReturn.poppedMachine frames caller frame
    (ActualPopPlan.released (PtrMetadataReturn.accountedMachine options remaining span machine)
      releasedMemory tracker borrowFrame) (thread.topUserRelevantFrame.getD (frames.push caller).size)

variable (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (tracker : MachineHooks.BorrowState)
    (borrowFrame : FrameState)
    (releasedMemory : MemoryState Provenance BorrowTree MiriMemoryKind) (thread : ThreadRecord)

 theorem memory_eq :
    (finalMachine options remaining span frames caller frame machine tracker borrowFrame releasedMemory thread).memory =
      releasedMemory := by
  simp only [finalMachine,PtrMetadataReturn.poppedMachine,GenericPopFrame.afterRelevanceAt]
  split <;> rfl

 theorem tracked :
    (finalMachine options remaining span frames caller frame machine tracker borrowFrame releasedMemory thread).borrowTracker =
      some {tracker with global := tracker.global.endCall borrowFrame} := by
  simp only [finalMachine,PtrMetadataReturn.poppedMachine,GenericPopFrame.afterRelevanceAt]
  split <;> rfl

 theorem user_eq :
    (finalMachine options remaining span frames caller frame machine tracker borrowFrame releasedMemory thread).user =
      (PtrMetadataReturn.accountedMachine options remaining span machine).user := by
  unfold finalMachine
  rw [PtrMetadataReturn.popped_user]
  rfl

 theorem ghost_eq :
    (finalMachine options remaining span frames caller frame machine tracker borrowFrame releasedMemory thread).user.payload.ghost =
      machine.user.payload.ghost := by
  rw [user_eq]
  exact PtrMetadataReturn.accounted_ghost options remaining span machine

 theorem validation_eq :
    (finalMachine options remaining span frames caller frame machine tracker borrowFrame releasedMemory thread).user.payload.validation =
      machine.user.payload.validation := by
  rw [user_eq]
  exact PtrMetadataReturn.accounted_validation options remaining span machine

 theorem race_eq :
    (finalMachine options remaining span frames caller frame machine tracker borrowFrame releasedMemory thread).dataRace = machine.dataRace := by
  simp only [finalMachine,PtrMetadataReturn.poppedMachine,GenericPopFrame.afterRelevanceAt]
  split <;> rfl

 theorem fixed_eq :
    (finalMachine options remaining span frames caller frame machine tracker borrowFrame releasedMemory thread).threads.fixedScheduling =
      machine.threads.fixedScheduling := by
  simp only [finalMachine,PtrMetadataReturn.poppedMachine,GenericPopFrame.afterRelevanceAt]
  split <;> rfl

 theorem unchecked
    (source : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false) :
    ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      (finalMachine options remaining span frames caller frame machine tracker borrowFrame releasedMemory thread).user).checkedArithmetic = false := by
  rw [user_eq]
  unfold PtrMetadataReturn.accountedMachine SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators] at source ⊢
  exact source

 theorem no_gc
    (source : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0) :
    ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      (finalMachine options remaining span frames caller frame machine tracker borrowFrame releasedMemory thread).user).gcInterval = 0 := by
  rw [user_eq]
  unfold PtrMetadataReturn.accountedMachine SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators] at source ⊢
  exact source

 theorem active_exists (source : machine.threads.activeThread? = some thread) :
    ∃ result, (finalMachine options remaining span frames caller frame machine tracker borrowFrame releasedMemory thread).threads.activeThread? = some result := by
  let released := ActualPopPlan.released (PtrMetadataReturn.accountedMachine options remaining span machine)
    releasedMemory tracker borrowFrame
  have known : released.threads.activeThread? = some thread := source
  simp only [finalMachine,PtrMetadataReturn.poppedMachine,GenericPopFrame.afterRelevanceAt]
  split
  · exact ⟨_,MetadataOutputFacts.relevance_active (frames.push caller) frame released thread known⟩
  · exact ⟨thread,known⟩

 theorem addresses_eq :
    (finalMachine options remaining span frames caller frame machine tracker borrowFrame releasedMemory thread).user.addresses =
      machine.user.addresses := by
  rw [user_eq]
  unfold PtrMetadataReturn.accountedMachine SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  rfl

 theorem types_eq :
    (finalMachine options remaining span frames caller frame machine tracker borrowFrame releasedMemory thread).user.payload.payload.user.types =
      machine.user.payload.payload.user.types := by
  rw [user_eq]
  unfold PtrMetadataReturn.accountedMachine SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  rfl

 theorem backend_eq :
    (finalMachine options remaining span frames caller frame machine tracker borrowFrame releasedMemory thread).user.payload.payload.user.backend =
      machine.user.payload.payload.user.backend := by
  rw [user_eq]
  unfold PtrMetadataReturn.accountedMachine SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  rfl

 theorem extras_eq :
    (finalMachine options remaining span frames caller frame machine tracker borrowFrame releasedMemory thread).user.payload.payload.user.runtime.extras =
      machine.user.payload.payload.user.runtime.extras := by
  rw [user_eq]
  unfold PtrMetadataReturn.accountedMachine SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  rfl

 theorem arrays_eq
    (afterFrames beforeFrames : Array CompilerFrameContext.ActualFrame)
    (afterFrame beforeFrame : CompilerFrameContext.ActualFrame) :
    EvalProjectionMachine.arrays.get (Storage.withCurrent afterFrames afterFrame
      (finalMachine options remaining span frames caller frame machine tracker borrowFrame releasedMemory thread)) =
    EvalProjectionMachine.arrays.get (Storage.withCurrent beforeFrames beforeFrame machine) := by
  change (finalMachine options remaining span frames caller frame machine tracker borrowFrame releasedMemory thread).user.payload.payload.user.types =
    machine.user.payload.payload.user.types
  rw [user_eq]
  unfold PtrMetadataReturn.accountedMachine SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  rfl

end
end DuplicatePrefix.EmptyForestLenReturnState
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.EmptyForestLenReturnState." then
      for dependency in (←collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved len return state {dependency}"
