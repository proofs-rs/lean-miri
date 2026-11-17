import duplicate_prefix.LenEntryFacts
import duplicate_prefix.RootArgumentEntry
namespace DuplicatePrefix.LenDone
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
open CallEntryFacts
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
theorem storage_live_slot (hooks : MachineHooks.StorageHooks K User)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K User) (localId : MIR.LocalId) (ty : MIR.TyId)
    (valid : localId < frame.locals.size) (typed : frame.body.locals[localId]? = some ty)
    (trivial : hooks.veryTriviallySized ty = .ok true)
    (dead : frame.locals[localId].value = .dead) (noClocks : frame.extra.dataRace = none) :
    MachineHooks.storageLiveDyn hooks localId .none (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore (liveSlot frame localId) machine) := by
  have step := Storage.storage_live_dead hooks framesBefore frame machine localId ty
    valid typed trivial dead noClocks
  simpa [liveSlot, Array.modify, Array.modifyM, valid] using step

theorem start_location (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (body : frame.body = LenHelper.body.body) :
    frame.setLocation (.mir .start) = .ok {frame with location := .mir .start} := by
  unfold Frame.setLocation
  rw [body]
  with_unfolding_all rfl

theorem stack_start_location
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (body : frame.body = LenHelper.body.body) :
    (⟨framesBefore.push frame⟩ : Stack Provenance LocalLayout MachineHooks.FrameExtra).updateCurrentLocation
      (.mir .start) = .ok ⟨framesBefore.push {frame with location := .mir .start}⟩ := by
  simp [Stack.updateCurrentLocation, start_location frame body, Array.set_push]
  rfl


def doneFrame (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) :=
  {liveSlot frame 0 with location := .mir .start}

theorem push_done (options : EvalConfigurationCore.Options) (choice : Unit) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = LenHelper.body.body) (valid : 0 < frame.locals.size)
    (dead : frame.locals[0].value = .dead) (noClocks : frame.extra.dataRace = none) :
    CallMachine.pushDone (PreparedContracts.actualConfig options choice remaining span).lifecycle
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames (doneFrame frame) machine) := by
  let cfg := PreparedContracts.actualConfig options choice remaining span
  have trivial : cfg.lifecycle.storage.veryTriviallySized 5 = .ok true := by
    rw [(CanonicalConfigFacts.actual_fields options choice remaining span).storage]
    exact RootCompilerFacts.root_storage_trivial_usize
  have h0 := storage_live_slot cfg.lifecycle.storage frames frame machine 0 5 valid
    (by rw [body]; rfl) trivial dead noClocks
  unfold CallMachine.pushDone
  simp only [bind, EStateM.bind]
  rw [h0]
  dsimp only
  rw [Storage.current_frame]
  dsimp only
  have always : CallMachine.alwaysLiveVarsAndTemps (liveSlot frame 0).body = .ok #[] := by
    simpa only [liveSlot, body] using LenEntryFacts.always_live
  rw [always]
  simp only [pure]
  simp [← Array.forIn_toList, bind, EStateM.bind, pure, EStateM.pure]
  simp only [get, getThe, MonadStateOf.get, EStateM.get, Storage.withCurrent]
  rw [stack_start_location frames _ (by simpa only [liveSlot] using body)]
  rfl
end DuplicatePrefix.LenDone
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.LenDone.push_done) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved metadata push-done dependency {dependency}"
