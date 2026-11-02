import duplicate_prefix.RootZeroCompleteState
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace DuplicatePrefix.EmptyRootSafetyInitialState
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

def guardFrame (frame : CompilerFrameContext.ActualFrame) (size : frame.locals.size=25) (count : UInt64) :=
  let storage := RootPrefix.afterStorageFrame frame size
  let copied := RootCopyCount.postFrame storage (by simp [storage,RootPrefix.afterStorageFrame,SourceSteps.liveFrame,size]) count
  RootEqStepSuccess.postFrame copied (by simp [copied,storage,RootCopyCount.postFrame,RootCopyCount.writeFrame,
    LocalPlaces.cachePlaceLayout,RootPrefix.afterStorageFrame,SourceSteps.liveFrame,size]) count

theorem shape (frame : CompilerFrameContext.ActualFrame) (size : frame.locals.size=25) (count : UInt64) :
    let after := guardFrame frame size count
    after.body=frame.body ∧ after.bodyIdentity=frame.bodyIdentity ∧ after.functionInstance=frame.functionInstance ∧
    after.extra=frame.extra ∧ after.returnPlace=frame.returnPlace ∧ after.returnContinuation=frame.returnContinuation ∧
    after.vaList=frame.vaList ∧ after.localsIdentity=frame.localsIdentity ∧ after.locals.size=25 ∧
    after.location=.mir ⟨0,5⟩ ∧ after.locals[0]?=frame.locals[0]? ∧ after.locals[1]?=frame.locals[1]? ∧
    after.locals[2]?=frame.locals[2]? ∧
    after.locals[3]?.map (·.value)=some (.live (.immediate .uninit)) ∧
    after.locals[4]?=some ⟨.live (.immediate (.scalar (.fromBool (count==0)))),some RootCompilerFacts.boolLayout⟩ ∧
    after.locals[5]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ ∧
    (∀ id,id≠3→id≠4→id≠5→after.locals[id]?=frame.locals[id]?) := by
  simp [guardFrame,RootPrefix.afterStorageFrame,SourceSteps.liveFrame,RootCopyCount.postFrame,RootCopyCount.writeFrame,
    RootEqStepSuccess.postFrame,LocalPlaces.cachePlaceLayout,size]
  all_goals
    intro id not3 not4 not5
    simp [Ne.symm not3,Ne.symm not4,Ne.symm not5]

theorem slot3 (frame : CompilerFrameContext.ActualFrame) (size : frame.locals.size=25) (count : UInt64)
    (cache : (frame.locals[3]'(by rw [size];decide)).layout=none) :
    (guardFrame frame size count).locals[3]?=some ⟨.live (.immediate .uninit),none⟩ := by
  simp [guardFrame,RootPrefix.afterStorageFrame,SourceSteps.liveFrame,RootCopyCount.postFrame,RootCopyCount.writeFrame,
    RootEqStepSuccess.postFrame,LocalPlaces.cachePlaceLayout,size,cache]

theorem all (frame : CompilerFrameContext.ActualFrame) (size : frame.locals.size=25) (count : UInt64)
    (before : CopyHelperCleanup.AllImmediate frame) : CopyHelperCleanup.AllImmediate (guardFrame frame size count) := by
  unfold guardFrame
  apply RootZeroCompleteState.all_guard
  apply RootZeroCompleteState.all_count
  unfold RootPrefix.afterStorageFrame
  apply RootZeroCompleteState.all_live
  apply RootZeroCompleteState.all_live
  apply RootZeroCompleteState.all_live
  exact before

#print axioms shape
end DuplicatePrefix.EmptyRootSafetyInitialState
open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.EmptyRootSafetyInitialState.shape,``DuplicatePrefix.EmptyRootSafetyInitialState.slot3,``DuplicatePrefix.EmptyRootSafetyInitialState.all] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved generic first-block state dependency {dependency}"
