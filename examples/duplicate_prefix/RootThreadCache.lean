import duplicate_prefix.MetadataOutputFacts
namespace DuplicatePrefix.RootThreadCache
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Concurrency
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem compute_pair (caller done : CompilerFrameContext.ActualFrame) :
    FrameRelevance.computeTop ⟨#[caller,done]⟩ 1 = some 0 := by
  simp [FrameRelevance.computeTop,List.range_succ,List.range_zero,Id.run]
  split <;> rfl

theorem pop_active (machine : MachineHooks.MachineState K U) (caller done : CompilerFrameContext.ActualFrame)
    (thread : ThreadRecord) (newRank oldRank : UInt8)
    (active : machine.threads.activeThread? = some (PushThread.after thread 1 newRank oldRank))
    (cached : thread.topUserRelevantFrame = some 0) :
    (GenericPopFrame.afterRelevanceAt #[caller] done machine
      ((PushThread.after thread 1 newRank oldRank).topUserRelevantFrame.getD 1)).threads.activeThread? = some thread := by
  have restore : {thread with topUserRelevantFrame := some 0} = thread := by rw [← cached]
  by_cases higher : newRank >= oldRank
  · simp only [PushThread.after,if_pos higher,Option.getD_some,GenericPopFrame.afterRelevanceAt,Array.size_singleton,if_true] at active ⊢
    have known := MetadataOutputFacts.relevance_active #[caller] done machine {thread with topUserRelevantFrame := some 1} active
    change (GenericPopFrame.afterRelevance #[caller] done machine).threads.activeThread? =
      some {thread with topUserRelevantFrame := FrameRelevance.computeTop ⟨#[caller,done]⟩ 1} at known
    rw [compute_pair,restore] at known
    exact known
  · simp only [PushThread.after,if_neg higher,cached,Option.getD_some,GenericPopFrame.afterRelevanceAt,Array.size_singleton] at active ⊢
    exact active
end DuplicatePrefix.RootThreadCache
open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.RootThreadCache.compute_pair,``DuplicatePrefix.RootThreadCache.pop_active] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved actual root thread-cache dependency {dependency}"
