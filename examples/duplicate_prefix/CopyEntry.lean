import duplicate_prefix.CopyHelperUnit
import duplicate_prefix.CopyTail
import duplicate_prefix.CopyPush
import duplicate_prefix.RootCallerLocation
import duplicate_prefix.CallLocalRead
namespace DuplicatePrefix.CopyEntry
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CanonicalConfigFacts
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable def rawRoot (state : RootState) (destination : RuntimeStackPlace Provenance)
    (cont : ReturnContinuation) (race : state.machine.dataRace = none) : CopyFrameData.RootFrame :=
  CopyFrameData.raw (CallEntryFacts.freshRoot state.machine).1 destination cont (CallEntryFacts.freshRoot state.machine).2 race
noncomputable def initialized (state : RootState) (destination : RuntimeStackPlace Provenance)
    (cont : ReturnContinuation) (race : state.machine.dataRace = none) (source targetPointer : Scalar Provenance) (n : UInt64) :=
  CopyDone.doneFrame {(CopyInstall.result (CopyTail.trackedRoot (rawRoot state destination cont race)
    (RootCallerLocation.sourceInfo 8).span) source targetPointer n).frame with location := .unwinding CopyEntryFacts.copyPreamble}
 theorem raw_locals (state : RootState) (destination : RuntimeStackPlace Provenance)
    (cont : ReturnContinuation) (race : state.machine.dataRace = none) :
    (rawRoot state destination cont race).frame.locals = Array.replicate 17 (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
  with_unfolding_all rfl
 theorem actual_entry (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (debug : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (source targetPointer : Scalar Provenance) (n : UInt64) (callerId : MIR.LocalId) (valid : callerId < caller.locals.size)
    (old : Immediate Provenance) (live : caller.locals[callerId].value = .live (.immediate old))
    (cached : caller.locals[callerId].layout = some CopyHelperUnit.layout)
    (noClocks : caller.extra.dataRace = none) (noRace : machine.dataRace = none)
    (body : caller.body = RootBody.reflected.body.body) (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance) (trackNone : caller.trackCallerArg = none)
    (location : caller.location = .mir ⟨8,RootCallerLocation.statementCount 8⟩)
    (fuel : Nat) (validationFuel : options.limits.validation = fuel+1)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (thread : Miri.Concurrency.ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (index : Nat) (top : thread.topUserRelevantFrame = some index)
    (cachedFrame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (indexValid : index < (frames.push caller).size) (lookup : (frames.push caller)[index]? = some cachedFrame)
    (relevant : cachedFrame.extra.userRelevance > 0)
    (budget : Nat) (budgetEq : limits.callDispatch = budget+1) (cont : ReturnContinuation) :
    Call.initStackFrame (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      HelperCompilerFacts.copyCall.callee HelperCompilerFacts.copyBody HelperCompilerFacts.copyAbi
      #[.Copy (CopyInstall.first source),.Copy (CopyInstall.second targetPointer),.Copy (CopyInstall.third n)] true
      (LocalPlaces.localRuntimePlace frames.size caller callerId CopyHelperUnit.layout).stackView cont
      (Storage.withCurrent frames caller machine) =
      .ok () (Storage.withCurrent (frames.push caller)
        (initialized (Storage.withCurrent frames caller machine)
          (LocalPlaces.localRuntimePlace frames.size caller callerId CopyHelperUnit.layout).stackView cont noRace source targetPointer n)
        (CallEntryFacts.freshRoot machine).1) := by
  let state := Storage.withCurrent frames caller machine
  let destination := (LocalPlaces.localRuntimePlace frames.size caller callerId CopyHelperUnit.layout).stackView
  let root := rawRoot state destination cont noRace
  let postMachine := (CallEntryFacts.freshRoot machine).1
  have callerLocation := RootCallerLocation.actual_caller_at_copy options limits (remaining+1) span budget budgetEq
    frames caller machine body identity callee trackNone location
  have read := CallLocalRead.place_to_op_cached options limits (remaining+1) span debug frames caller machine callerId
    CopyHelperUnit.layout old valid live cached (by decide +kernel) noClocks ghost
  have pushed := CopyPush.actual_push options limits (remaining+1) span debug state destination cont thread active index top
    cachedFrame indexValid lookup relevant
  change _ = (EStateM.Result.ok () (Storage.withCurrent (frames.push caller) root.frame postMachine) : EStateM.Result StepError RootState Unit) at pushed
  have rawLocals : root.frame.locals = Array.replicate 17 (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := raw_locals state destination cont noRace
  have dead0 : (root.frame.locals[0]'(root.valid ⟨0,by decide⟩)).value = .dead := by simp only [rawLocals,Array.getElem_replicate]
  have dead : ∀ arg : Fin 3, (root.frame.locals[arg.val+1]'(root.valid (CopyInstall.argId arg))).value = .dead := by
    intro arg
    simp only [rawLocals,Array.getElem_replicate]
  have uncached : ∀ arg : Fin 3, (root.frame.locals[arg.val+1]'(root.valid (CopyInstall.argId arg))).layout = none := by
    intro arg
    simp only [rawLocals,Array.getElem_replicate]
  have tail := CopyTail.run options limits remaining span debug (frames.push caller) root postMachine tracker tracked
    source targetPointer n old CopyHelperUnit.layout CopyEntryFacts.copyPreamble (RootCallerLocation.sourceInfo 8).span
    rfl dead0 dead uncached fuel validationFuel ghost shallow
  rw [CopyCallCore.actual_entry_eq,CopyTail.core_eq]
  simp only [bind,EStateM.bind]
  rw [callerLocation]
  simp only [EStateM.bind]
  rw [read]
  simp only [EStateM.bind]
  dsimp only [state,destination] at pushed
  rw [pushed]
  simp only [EStateM.bind]
  exact tail
end DuplicatePrefix.CopyEntry
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.CopyEntry.actual_entry) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved complete add entry dependency {dependency}"
