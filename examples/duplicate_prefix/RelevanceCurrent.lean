import duplicate_prefix.GenericPushRelevance
namespace DuplicatePrefix.RelevanceCurrent
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.Concurrency
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

theorem exists_current (frames : Array CompilerFrameContext.ActualFrame) (thread : ThreadRecord)
    (nonempty : 0 < frames.size)
    (bound : ∀ index, thread.topUserRelevantFrame = some index → index < frames.size) :
    ∃ index current, FrameRelevance.top ⟨frames⟩ thread.topUserRelevantFrame = some index ∧ frames[index]? = some current := by
  cases cached : thread.topUserRelevantFrame with
  | none =>
    have valid : frames.size-1 < frames.size := by omega
    refine ⟨frames.size-1,frames[frames.size-1],?_,?_⟩
    · have notEmpty : frames ≠ #[] := by intro bad;rw [bad] at nonempty;cases nonempty
      simp [FrameRelevance.top,cached,notEmpty]
    · simp [valid]
  | some index =>
    have valid := bound index cached
    refine ⟨index,frames[index],?_,?_⟩
    · simp [FrameRelevance.top,cached]
    · simp [valid]
end DuplicatePrefix.RelevanceCurrent
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.RelevanceCurrent.exists_current) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved relevance data selection dependency {dependency}"
