import duplicate_prefix.AsMutPush
namespace DuplicatePrefix.AsMutPushPreserves
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
open CanonicalConfigFacts
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem user_after_push (machine : MachineHooks.MachineState K U) (size : Nat) (newRank oldRank : UInt8) :
    (GenericPushRelevance.afterPush machine size newRank oldRank).user = machine.user := by
  unfold GenericPushRelevance.afterPush
  split <;> rfl

theorem preserves (crates : Array Nat) (state : RootState) (destination : RuntimeStackPlace Provenance)
    (current : CompilerFrameContext.ActualFrame) :
    let post := (AsMutPush.completed crates state destination current).machine
    post.memory = state.machine.memory ∧ post.borrowTracker = state.machine.borrowTracker ∧
    post.dataRace = state.machine.dataRace ∧
    post.user.addresses = state.machine.user.addresses ∧
    post.user.payload.ghost = state.machine.user.payload.ghost ∧
    post.user.payload.validation = state.machine.user.payload.validation ∧
    post.user.payload.payload.user = state.machine.user.payload.payload.user ∧
    post.threads.fixedScheduling = state.machine.threads.fixedScheduling := by
  dsimp only [AsMutPush.completed,Storage.withCurrent]
  unfold GenericPushRelevance.afterPush
  split <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem active_cache (machine : MachineHooks.MachineState K U) (thread : Miri.Concurrency.ThreadRecord)
    (active : machine.threads.activeThread? = some thread) (size : Nat) :
    (CallEntryFacts.cacheTop machine size).threads.activeThread? = some {thread with topUserRelevantFrame := some size} := by
  change machine.threads.threads[machine.threads.activeThread.toNat]? = some thread at active
  change ((machine.threads.threads.mapIdx (fun position item =>
    if position == machine.threads.activeThread.toNat then {item with topUserRelevantFrame := some size} else item))[machine.threads.activeThread.toNat]?) = _
  simp only [List.getElem?_mapIdx,active,Option.map_some,beq_self_eq_true,ite_true]

theorem active_after_push (machine : MachineHooks.MachineState K U) (thread : Miri.Concurrency.ThreadRecord)
    (active : machine.threads.activeThread? = some thread) (size : Nat) (newRank oldRank : UInt8) :
    (GenericPushRelevance.afterPush machine size newRank oldRank).threads.activeThread? =
      some (if newRank >= oldRank then {thread with topUserRelevantFrame := some size} else thread) := by
  unfold GenericPushRelevance.afterPush
  split
  · exact active_cache machine thread active size
  · exact active

open Lean Elab Command in
run_cmd do
  for declaration in [``user_after_push,``preserves,``active_cache,``active_after_push] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved asmut push preservation dependency {dependency}"
end
end DuplicatePrefix.AsMutPushPreserves
