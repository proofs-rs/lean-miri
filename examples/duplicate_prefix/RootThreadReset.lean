import duplicate_prefix.RootThreadCache
namespace DuplicatePrefix.RootThreadReset
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Concurrency
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
theorem pop_cache_zero (machine : MachineHooks.MachineState K U)
    (caller done : CompilerFrameContext.ActualFrame) (thread : ThreadRecord)
    (index : Nat) (bound : index < 2)
    (active : machine.threads.activeThread? = some {thread with topUserRelevantFrame := some index}) :
    (GenericPopFrame.afterRelevanceAt #[caller] done machine index).threads.activeThread? =
      some {thread with topUserRelevantFrame := some 0} := by
  have cases : index = 0 ∨ index = 1 := by omega
  rcases cases with rfl | rfl
  · simpa only [GenericPopFrame.afterRelevanceAt,Array.size_singleton,Nat.zero_ne_one,↓reduceIte] using active
  · have known := MetadataOutputFacts.relevance_active #[caller] done machine
      {thread with topUserRelevantFrame := some 1} active
    have computed : FrameRelevance.computeTop ⟨#[caller].push done⟩ 1 = some 0 := RootThreadCache.compute_pair caller done
    rw [computed] at known
    simpa only [GenericPopFrame.afterRelevanceAt,Array.size_singleton,↓reduceIte] using known
end DuplicatePrefix.RootThreadReset
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.RootThreadReset.pop_cache_zero) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved thread cache reset {dependency}"
