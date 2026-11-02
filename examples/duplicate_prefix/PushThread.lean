import duplicate_prefix.GenericPushRelevance
namespace DuplicatePrefix.PushThread
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.Concurrency
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

def after (thread : ThreadRecord) (index : Nat) (newRank oldRank : UInt8) :=
  if newRank >= oldRank then {thread with topUserRelevantFrame := some index} else thread

theorem cache_top_active (machine : MachineHooks.MachineState K User) (thread : ThreadRecord) (index : Nat)
    (active : machine.threads.activeThread? = some thread) :
    (CallEntryFacts.cacheTop machine index).threads.activeThread? =
      some {thread with topUserRelevantFrame := some index} := by
  have lookup : machine.threads.threads[machine.threads.activeThread.toNat]? = some thread := active
  unfold CallEntryFacts.cacheTop ThreadManager.activeThread?
  unfold_internal ".ThreadManager.get?"
  simp [List.getElem?_mapIdx,lookup]

theorem active_after (machine : MachineHooks.MachineState K User) (thread : ThreadRecord) (index : Nat)
    (newRank oldRank : UInt8) (active : machine.threads.activeThread? = some thread) :
    (GenericPushRelevance.afterPush machine index newRank oldRank).threads.activeThread? =
      some (after thread index newRank oldRank) := by
  unfold GenericPushRelevance.afterPush after
  split
  · exact cache_top_active machine thread index active
  · exact active
end DuplicatePrefix.PushThread
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.PushThread.active_after) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved pushed-thread dependency {dependency}"
