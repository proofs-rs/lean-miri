import duplicate_prefix.AddTail
import duplicate_prefix.AddPush
import duplicate_prefix.RootCallerLocation
import duplicate_prefix.CallLocalRead
namespace DuplicatePrefix.AddEntry
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CanonicalConfigFacts
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable def rawRoot (state : RootState) (destination : RuntimeStackPlace Provenance)
    (cont : ReturnContinuation) (race : state.machine.dataRace = none) : AddFrameData.RootFrame :=
  AddFrameData.raw (CallEntryFacts.freshRoot state.machine).1 destination cont (CallEntryFacts.freshRoot state.machine).2 race
noncomputable def initialized (state : RootState) (destination : RuntimeStackPlace Provenance)
    (cont : ReturnContinuation) (race : state.machine.dataRace = none) (pointer : Scalar Provenance) (n : UInt64) :=
  AddDone.doneFrame {(AddInstall.result (AddTail.trackedRoot (rawRoot state destination cont race)
    (RootCallerLocation.sourceInfo 7).span) pointer n).frame with location := .unwinding AddEntryFacts.addPreamble}
 theorem raw_locals (state : RootState) (destination : RuntimeStackPlace Provenance)
    (cont : ReturnContinuation) (race : state.machine.dataRace = none) :
    (rawRoot state destination cont race).frame.locals = Array.replicate 5 (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
  with_unfolding_all rfl
 theorem actual_entry (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (debug : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (pointer : Scalar Provenance) (n : UInt64) (callerId : MIR.LocalId) (valid : callerId < caller.locals.size)
    (old : Immediate Provenance) (live : caller.locals[callerId].value = .live (.immediate old))
    (cached : caller.locals[callerId].layout = some CopyCompilerFacts.destPointerLayout)
    (noClocks : caller.extra.dataRace = none) (noRace : machine.dataRace = none)
    (body : caller.body = RootBody.reflected.body.body) (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance) (trackNone : caller.trackCallerArg = none)
    (location : caller.location = .mir ⟨7,RootCallerLocation.statementCount 7⟩)
    (fuel : Nat) (validationFuel : options.limits.validation = fuel+1)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (thread : Miri.Concurrency.ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (index : Nat) (top : thread.topUserRelevantFrame = some index)
    (cachedFrame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (indexValid : index < (frames.push caller).size) (lookup : (frames.push caller)[index]? = some cachedFrame)
    (relevant : cachedFrame.extra.userRelevance > 0)
    (budget : Nat) (budgetEq : limits.callDispatch = budget+1) (cont : ReturnContinuation) :
    Call.initStackFrame (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      HelperCompilerFacts.addCall.callee HelperCompilerFacts.addBody HelperCompilerFacts.addAbi
      #[.Copy (AddInstall.first pointer),.Copy (AddInstall.second n)] true
      (LocalPlaces.localRuntimePlace frames.size caller callerId CopyCompilerFacts.destPointerLayout).stackView cont
      (Storage.withCurrent frames caller machine) =
      .ok () (Storage.withCurrent (frames.push caller)
        (initialized (Storage.withCurrent frames caller machine)
          (LocalPlaces.localRuntimePlace frames.size caller callerId CopyCompilerFacts.destPointerLayout).stackView cont noRace pointer n)
        (CallEntryFacts.freshRoot machine).1) := by
  let state := Storage.withCurrent frames caller machine
  let destination := (LocalPlaces.localRuntimePlace frames.size caller callerId CopyCompilerFacts.destPointerLayout).stackView
  let root := rawRoot state destination cont noRace
  let postMachine := (CallEntryFacts.freshRoot machine).1
  have callerLocation := RootCallerLocation.actual_caller_at_add options limits (remaining+1) span budget budgetEq
    frames caller machine body identity callee trackNone location
  have read := CallLocalRead.place_to_op_cached options limits (remaining+1) span debug frames caller machine callerId
    CopyCompilerFacts.destPointerLayout old valid live cached (by decide +kernel) noClocks ghost
  have pushed := AddPush.actual_push options limits (remaining+1) span debug state destination cont thread active index top
    cachedFrame indexValid lookup relevant
  change _ = (EStateM.Result.ok () (Storage.withCurrent (frames.push caller) root.frame postMachine) : EStateM.Result StepError RootState Unit) at pushed
  have rawLocals : root.frame.locals = Array.replicate 5 (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := raw_locals state destination cont noRace
  have dead0 : (root.frame.locals[0]'(root.valid ⟨0,by decide⟩)).value = .dead := by simp only [rawLocals,Array.getElem_replicate]
  have dead1 : (root.frame.locals[1]'(root.valid AddInstall.i1)).value = .dead := by simp only [rawLocals,Array.getElem_replicate]
  have dead2 : (root.frame.locals[2]'(root.valid AddInstall.i2)).value = .dead := by simp only [rawLocals,Array.getElem_replicate]
  have cache1 : (root.frame.locals[1]'(root.valid AddInstall.i1)).layout = none := by simp only [rawLocals,Array.getElem_replicate]
  have cache2 : (root.frame.locals[2]'(root.valid AddInstall.i2)).layout = none := by simp only [rawLocals,Array.getElem_replicate]
  have tail := AddTail.run options limits remaining span debug (frames.push caller) root postMachine tracker tracked
    pointer n old CopyCompilerFacts.destPointerLayout AddEntryFacts.addPreamble (RootCallerLocation.sourceInfo 7).span
    rfl dead0 dead1 cache1 dead2 cache2 fuel validationFuel ghost shallow
  rw [AddCallCore.actual_entry_eq,AddTail.core_eq]
  simp only [bind,EStateM.bind]
  rw [callerLocation]
  simp only [EStateM.bind]
  rw [read]
  simp only [EStateM.bind]
  dsimp only [state,destination] at pushed
  rw [pushed]
  simp only [EStateM.bind]
  exact tail
end DuplicatePrefix.AddEntry
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.AddEntry.actual_entry) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved complete add entry dependency {dependency}"
