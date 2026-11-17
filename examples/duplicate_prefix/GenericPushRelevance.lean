import duplicate_prefix.CallEntryFacts
namespace DuplicatePrefix.GenericPushRelevance
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
noncomputable def afterPush (machine : MachineHooks.MachineState K User) (size : Nat)
    (newRank oldRank : UInt8) :=
  if newRank >= oldRank then CallEntryFacts.cacheTop machine size else machine

theorem after_push (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame current : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K User) (thread : Miri.Concurrency.ThreadRecord) (index : Nat)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top ⟨frames.push frame⟩ thread.topUserRelevantFrame = some index)
    (present : (frames.push frame)[index]? = some current) :
    FrameRelevance.afterStackPush false (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames frame (afterPush machine frames.size frame.extra.userRelevance current.extra.userRelevance)) := by
  unfold FrameRelevance.afterStackPush
  unfold_relevance_helpers
  simp [MachineHooks.currentFrame, Storage.withCurrent, Stack.currentFrame?,
    Array.back?_push, active, top, present, afterPush,
    bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    pure, EStateM.pure, CallEntryFacts.cacheTop]
  split <;> simp_all [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, pure, EStateM.pure,
    CallEntryFacts.cacheTop, Storage.withCurrent]
end DuplicatePrefix.GenericPushRelevance

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.GenericPushRelevance.after_push) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved push relevance dependency {dependency}"
