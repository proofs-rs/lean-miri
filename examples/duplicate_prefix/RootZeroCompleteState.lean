import duplicate_prefix.RootBlock0
import duplicate_prefix.RootZeroCompleteBranch
import duplicate_prefix.RootZeroCompleteSwitch
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace DuplicatePrefix.RootZeroCompleteState
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

noncomputable def tick (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :=
  (SourceControl.accounted (PreparedContracts.actualConfig options () (remaining+1) span).terminators
    (⟨⟨#[]⟩,machine⟩ : MachineHooks.State MiriMemoryKind Machine.RootUser)).machine

theorem tick_ghost (options remaining span machine) :
    (tick options remaining span machine).user.payload.ghost = machine.user.payload.ghost := by
  unfold tick SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  rfl

theorem tick_shallow (options remaining span machine) :
    (tick options remaining span machine).user.payload.validation = machine.user.payload.validation := by
  unfold tick SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  rfl

theorem tick_flags (options remaining span machine) :
    let hooks := (PreparedContracts.actualConfig options () (remaining+1) span).terminators
    (hooks.getControl (tick options remaining span machine).user).checkedArithmetic = (hooks.getControl machine.user).checkedArithmetic ∧
    (hooks.getControl (tick options remaining span machine).user).gcInterval = (hooks.getControl machine.user).gcInterval := by
  dsimp only
  unfold tick SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  exact ⟨rfl,rfl⟩

def guardFrame (frame : CompilerFrameContext.ActualFrame) (size : frame.locals.size = 25) :=
  let storage := RootPrefix.afterStorageFrame frame size
  let count := RootCopyCount.postFrame storage (by simp [storage,RootPrefix.afterStorageFrame,SourceSteps.liveFrame,size]) 0
  RootEqStepSuccess.postFrame count (by simp [count,storage,RootCopyCount.postFrame,RootCopyCount.writeFrame,
    LocalPlaces.cachePlaceLayout,RootPrefix.afterStorageFrame,SourceSteps.liveFrame,size]) 0

theorem guard_shape (frame : CompilerFrameContext.ActualFrame) (size : frame.locals.size = 25) :
    let after := guardFrame frame size
    after.body = frame.body ∧ after.bodyIdentity = frame.bodyIdentity ∧ after.functionInstance = frame.functionInstance ∧
    after.extra = frame.extra ∧ after.returnPlace = frame.returnPlace ∧ after.returnContinuation = frame.returnContinuation ∧
    after.vaList = frame.vaList ∧ after.localsIdentity = frame.localsIdentity ∧ after.locals.size = 25 ∧
    after.location = .mir ⟨0,5⟩ ∧ after.locals[0]? = frame.locals[0]? ∧
    after.locals[3]?.map (·.value) = some (.live (.immediate .uninit)) ∧
    after.locals[4]? = some ⟨.live (.immediate (.scalar (.fromBool true))),some RootCompilerFacts.boolLayout⟩ ∧
    after.locals[5]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 0)))),some RootCompilerFacts.usizeLayout⟩ := by
  simp [guardFrame,RootPrefix.afterStorageFrame,SourceSteps.liveFrame,RootCopyCount.postFrame,RootCopyCount.writeFrame,
    RootEqStepSuccess.postFrame,LocalPlaces.cachePlaceLayout,size,Array.getElem?_set,Array.getElem_set]

theorem all_live (frame : CompilerFrameContext.ActualFrame) (location : MIR.Location) (id : MIR.LocalId)
    (valid : id < frame.locals.size) (all : CopyHelperCleanup.AllImmediate frame) :
    CopyHelperCleanup.AllImmediate (SourceSteps.liveFrame frame location id valid) :=
  CopyHelperCleanup.all_immediate_set frame id _ valid all (by intro memory;simp)

theorem all_count (frame : CompilerFrameContext.ActualFrame) (valid : (5 : MIR.LocalId)<frame.locals.size)
    (n : UInt64) (all : CopyHelperCleanup.AllImmediate frame) :
    CopyHelperCleanup.AllImmediate (RootCopyCount.postFrame frame valid n) := by
  apply CopyHelperCleanup.all_immediate_set (LocalPlaces.cachePlaceLayout frame 5 RootCompilerFacts.usizeLayout valid) 5 _ (by simpa [LocalPlaces.cachePlaceLayout] using valid)
    (CopyHelperCleanup.all_immediate_cache frame 5 RootCompilerFacts.usizeLayout valid all)
  intro memory
  simp

theorem all_guard (frame : CompilerFrameContext.ActualFrame) (valid : (4 : MIR.LocalId)<frame.locals.size)
    (n : UInt64) (all : CopyHelperCleanup.AllImmediate frame) :
    CopyHelperCleanup.AllImmediate (RootEqStepSuccess.postFrame frame valid n) := by
  apply CopyHelperCleanup.all_immediate_set (LocalPlaces.cachePlaceLayout frame 4 RootCompilerFacts.boolLayout valid) 4 _ (by simpa [LocalPlaces.cachePlaceLayout] using valid)
    (CopyHelperCleanup.all_immediate_cache frame 4 RootCompilerFacts.boolLayout valid all)
  intro memory
  simp

theorem guard_all (frame : CompilerFrameContext.ActualFrame) (size : frame.locals.size=25)
    (all : CopyHelperCleanup.AllImmediate frame) : CopyHelperCleanup.AllImmediate (guardFrame frame size) := by
  unfold guardFrame
  apply all_guard
  apply all_count
  unfold RootPrefix.afterStorageFrame
  apply all_live
  apply all_live
  apply all_live
  exact all

#print axioms guard_shape
#print axioms tick_flags
end DuplicatePrefix.RootZeroCompleteState

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.RootZeroCompleteState.tick_ghost,
      ``DuplicatePrefix.RootZeroCompleteState.tick_shallow, ``DuplicatePrefix.RootZeroCompleteState.tick_flags,
      ``DuplicatePrefix.RootZeroCompleteState.guard_shape, ``DuplicatePrefix.RootZeroCompleteState.guard_all] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved root zero state dependency {dependency}"
