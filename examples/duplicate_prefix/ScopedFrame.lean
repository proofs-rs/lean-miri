import duplicate_prefix.MetadataCallCore
namespace DuplicatePrefix.ScopedFrame
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
open CanonicalConfigFacts
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

def entered (machine : MachineHooks.MachineState K User) (tracker : MachineHooks.BorrowState)
    (mode : TreeBorrows.RetagPolicy.RetagMode) :=
  {machine with borrowTracker := some {tracker with retagMode := mode}}

theorem same_machine (action : MachineHooks.M K User A)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (before after : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K User) (tracker : MachineHooks.BorrowState)
    (mode : TreeBorrows.RetagPolicy.RetagMode) (value : A)
    (tracked : machine.borrowTracker = some tracker)
    (body : action (Storage.withCurrent frames before (entered machine tracker mode)) =
      .ok value (Storage.withCurrent frames after (entered machine tracker mode))) :
    MachineHooks.withRetagMode mode action (Storage.withCurrent frames before machine) =
      .ok value (Storage.withCurrent frames after machine) := by
  unfold MachineHooks.withRetagMode
  simp only [Storage.withCurrent, tracked]
  change (match action (Storage.withCurrent frames before (entered machine tracker mode)) with
    | .ok result afterState => _
    | .error error afterState => _) = _
  rw [body]
  simp only [Storage.withCurrent, entered]
  have restore : {tracker with retagMode := tracker.retagMode} = tracker := by cases tracker; rfl
  try simp only [restore]
  rw [← tracked]
theorem changed_state (action : MachineHooks.M K User A)
    (before after : MachineHooks.State K User) (tracker nextTracker : MachineHooks.BorrowState)
    (mode : TreeBorrows.RetagPolicy.RetagMode) (value : A)
    (tracked : before.machine.borrowTracker = some tracker)
    (afterTracked : after.machine.borrowTracker = some nextTracker)
    (body : action {before with machine := entered before.machine tracker mode} = .ok value after) :
    MachineHooks.withRetagMode mode action before =
      .ok value {after with machine := {after.machine with borrowTracker := some {nextTracker with retagMode := tracker.retagMode}}} := by
  unfold MachineHooks.withRetagMode
  rw [tracked]
  dsimp only
  dsimp only [entered] at body
  rw [body]
  dsimp only
  rw [afterTracked]
end DuplicatePrefix.ScopedFrame
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.ScopedFrame.same_machine, ``DuplicatePrefix.ScopedFrame.changed_state] do
   for dependency in (← collectAxioms name) do
     unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
       throwError "unapproved scoped frame dependency {dependency}"
