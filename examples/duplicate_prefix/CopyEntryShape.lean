import duplicate_prefix.CopyEntry
import duplicate_prefix.CopyHelperCleanup
namespace DuplicatePrefix.CopyEntryShape
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
noncomputable section
 theorem locals (state : CanonicalConfigFacts.RootState) (destination : RuntimeStackPlace Provenance)
    (cont : ReturnContinuation) (race : state.machine.dataRace = none)
    (source targetPointer : Scalar Provenance) (n : UInt64) :
    (CopyEntry.initialized state destination cont race source targetPointer n).locals =
    #[⟨.live (.immediate .uninit),none⟩,
      ⟨.live (.immediate (.scalar source)),some CopyCompilerFacts.sourcePointerLayout⟩,
      ⟨.live (.immediate (.scalar targetPointer)),some CopyCompilerFacts.destPointerLayout⟩,
      ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))),some RootCompilerFacts.usizeLayout⟩] ++
      Array.replicate 13 ⟨.dead,none⟩ := by
  with_unfolding_all rfl
 theorem control (state : CanonicalConfigFacts.RootState) (destination : RuntimeStackPlace Provenance)
    (cont : ReturnContinuation) (race : state.machine.dataRace = none)
    (source targetPointer : Scalar Provenance) (n : UInt64) :
    let frame := CopyEntry.initialized state destination cont race source targetPointer n
    frame.body = HelperCompilerFacts.copyBody.body ∧ frame.bodyIdentity = HelperCompilerFacts.copyBody.identity ∧
    frame.functionInstance = HelperCompilerFacts.copyCall.callee ∧ frame.location = .mir ⟨0,0⟩ ∧
    frame.returnPlace = destination ∧ frame.returnContinuation = cont ∧ frame.vaList = #[] ∧
    frame.trackCallerArg = some (RootCallerLocation.sourceInfo 8).span := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
 theorem no_clocks (state : CanonicalConfigFacts.RootState) (destination : RuntimeStackPlace Provenance)
    (cont : ReturnContinuation) (race : state.machine.dataRace = none)
    (source targetPointer : Scalar Provenance) (n : UInt64) :
    (CopyEntry.initialized state destination cont race source targetPointer n).extra.dataRace = none := by
  simp only [CopyEntry.initialized,CopyDone.doneFrame,CallEntryFacts.liveSlot,
    CopyInstall.result,CopyInstall.completed,CopyInstall.cached,CopyFrameData.write,CopyFrameData.live,
    CopyFrameData.cache,CopyFrameData.atSpan,LocalOperands.cachedLayoutFrame,CopyTail.trackedRoot,
    CopyEntry.rawRoot,CopyFrameData.raw,TrackedFrame.raw,CallEntryFacts.freshRoot,race,Option.map_none]
 theorem borrow (state : CanonicalConfigFacts.RootState) (destination : RuntimeStackPlace Provenance)
    (cont : ReturnContinuation) (race : state.machine.dataRace = none)
    (source targetPointer : Scalar Provenance) (n : UInt64)
    (tracker : MachineHooks.BorrowState) (tracked : state.machine.borrowTracker = some tracker) :
    (CopyEntry.initialized state destination cont race source targetPointer n).extra.borrowTracker = some ({} : FrameState) := by
  simp only [CopyEntry.initialized,CopyDone.doneFrame,CallEntryFacts.liveSlot,
    CopyInstall.result,CopyInstall.completed,CopyInstall.cached,CopyFrameData.write,CopyFrameData.live,
    CopyFrameData.cache,CopyFrameData.atSpan,LocalOperands.cachedLayoutFrame,CopyTail.trackedRoot,
    CopyEntry.rawRoot,CopyFrameData.raw,TrackedFrame.raw,CallEntryFacts.freshRoot,tracked,Option.map_some]
 theorem all_immediate (state : CanonicalConfigFacts.RootState) (destination : RuntimeStackPlace Provenance)
    (cont : ReturnContinuation) (race : state.machine.dataRace = none)
    (source targetPointer : Scalar Provenance) (n : UInt64) :
    CopyHelperCleanup.AllImmediate (CopyEntry.initialized state destination cont race source targetPointer n) := by
  intro slot member memory
  rw [locals] at member
  simp [Array.mem_def] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> simp


end
end DuplicatePrefix.CopyEntryShape
open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.CopyEntryShape.locals, ``DuplicatePrefix.CopyEntryShape.control,
      ``DuplicatePrefix.CopyEntryShape.all_immediate, ``DuplicatePrefix.CopyEntryShape.no_clocks, ``DuplicatePrefix.CopyEntryShape.borrow] do
    for dependency in (←collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved copy entry shape {dependency}"
