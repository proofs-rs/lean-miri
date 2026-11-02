import duplicate_prefix.RootThreadCache
namespace DuplicatePrefix.GeneralBorrowForestAcceptedAfterLenCache
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Concurrency
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
/-- A real one-root helper pop restores root cache zero even if the optional
cache was absent. The bound is source thread metadata, not operation success. -/
theorem pop (machine : MachineHooks.MachineState K U) (caller done : CompilerFrameContext.ActualFrame)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (bound : ∀ index,thread.topUserRelevantFrame=some index → index<2) :
    ∃ finalThread,
      (GenericPopFrame.afterRelevanceAt #[caller] done machine (thread.topUserRelevantFrame.getD 1)).threads.activeThread? = some finalThread ∧
      finalThread.topUserRelevantFrame = some 0 := by
  have recompute : ∃ finalThread,
      (GenericPopFrame.afterRelevance #[caller] done machine).threads.activeThread? = some finalThread ∧
      finalThread.topUserRelevantFrame = some 0 := by
    have known := MetadataOutputFacts.relevance_active #[caller] done machine thread active
    change (GenericPopFrame.afterRelevance #[caller] done machine).threads.activeThread? =
      some {thread with topUserRelevantFrame := FrameRelevance.computeTop ⟨#[caller,done]⟩ 1} at known
    rw [RootThreadCache.compute_pair] at known
    exact ⟨_,known,rfl⟩
  cases cached : thread.topUserRelevantFrame with
  | none => simpa only [cached,Option.getD_none,GenericPopFrame.afterRelevanceAt,Array.size_singleton,ite_true] using recompute
  | some index =>
    have small := bound index cached
    by_cases zero : index = 0
    · subst index
      refine ⟨thread,?_,cached⟩
      simpa only [cached,Option.getD_some,GenericPopFrame.afterRelevanceAt,Array.size_singleton,show ¬((0 : Nat)=1) from by decide,ite_false] using active
    · have one : index = 1 := by omega
      subst index
      simpa only [cached,Option.getD_some,GenericPopFrame.afterRelevanceAt,Array.size_singleton,ite_true] using recompute
end DuplicatePrefix.GeneralBorrowForestAcceptedAfterLenCache
