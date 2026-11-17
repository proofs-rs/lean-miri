import duplicate_prefix.LanguageZeroSpans

/-! The actual runtime guard has one bool return local and no live source
    locals at the entry point. This is the production pushDone transition. -/
namespace DuplicatePrefix.LanguageZeroDone
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
open DuplicatePrefix
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

noncomputable def liveSlot (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) :=
  CallEntryFacts.liveSlot frame 0
noncomputable def doneFrame (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) :=
  {liveSlot frame with location := .mir .start}

private theorem storage_live_slot (hooks : MachineHooks.StorageHooks K User)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K User) (valid : 0 < frame.locals.size)
    (typed : frame.body.locals[0]? = some 0) (trivial : hooks.veryTriviallySized 0 = .ok true)
    (dead : frame.locals[0].value = .dead) (noClocks : frame.extra.dataRace = none) :
    MachineHooks.storageLiveDyn hooks 0 .none (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames (liveSlot frame) machine) := by
  have step := Storage.storage_live_dead hooks frames frame machine 0 0 valid typed trivial dead noClocks
  simpa [liveSlot, CallEntryFacts.liveSlot, Array.modify, Array.modifyM, valid] using step

theorem push_done (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = CopyPreconditions.Bodies.checkLanguage.loaded.body)
    (valid : 0 < frame.locals.size) (dead : frame.locals[0].value = .dead)
    (noClocks : frame.extra.dataRace = none) :
    CallMachine.pushDone (PreparedContracts.actualConfig options () remaining span).lifecycle
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames (doneFrame frame) machine) := by
  let cfg := PreparedContracts.actualConfig options () remaining span
  have trivial : cfg.lifecycle.storage.veryTriviallySized 0 = .ok true := by
    rw [(CanonicalConfigFacts.actual_fields options () remaining span).storage]
    exact RootCompilerFacts.root_storage_trivial_bool
  have storage := storage_live_slot cfg.lifecycle.storage frames frame machine valid
    (by rw [body]; rfl) trivial dead noClocks
  unfold CallMachine.pushDone
  simp only [bind, EStateM.bind]
  rw [storage]
  dsimp only
  rw [Storage.current_frame]
  dsimp only
  have always : CallMachine.alwaysLiveVarsAndTemps (liveSlot frame).body = .ok #[] := by
    simpa [liveSlot, CallEntryFacts.liveSlot, body] using GuardCompilerFacts.language_always_live
  rw [always]
  simp only [pure]
  simp [← Array.forIn_toList, bind, EStateM.bind, pure, EStateM.pure]
  simp only [get, getThe, MonadStateOf.get, EStateM.get, Storage.withCurrent]
  have liveBody : (liveSlot frame).body = CopyPreconditions.Bodies.checkLanguage.loaded.body := by
    simp [liveSlot, CallEntryFacts.liveSlot, body]
  have hasBlock : 0 < CopyPreconditions.Bodies.checkLanguage.loaded.body.basicBlocks.size := by decide +kernel
  have start : (liveSlot frame).setLocation (.mir .start) = .ok {liveSlot frame with location := .mir .start} := by
    simp [Frame.setLocation, MIR.Location.start, liveBody, hasBlock, pure, Except.pure]
  simp [Stack.updateCurrentLocation, start, Array.set_push, doneFrame]
  rfl

end
end DuplicatePrefix.LanguageZeroDone

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.LanguageZeroDone.push_done) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved runtime zero pushDone dependency {dependency}"
