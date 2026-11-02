import duplicate_prefix.GenericPopFrame

namespace DuplicatePrefix.PopActive
open Miri Miri.Interpreter Miri.Memory Miri.Concurrency
open DuplicatePrefix

def refreshedThread (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (thread : ThreadRecord) :=
  {thread with topUserRelevantFrame := FrameRelevance.computeTop ⟨frames.push frame⟩ 1}

theorem after_relevance_active
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K U) (thread : ThreadRecord)
    (active : machine.threads.activeThread? = some thread) :
    (GenericPopFrame.afterRelevance frames frame machine).threads.activeThread? =
      some (refreshedThread frames frame thread) := by
  have lookup : machine.threads.threads[machine.threads.activeThread.toNat]? = some thread := active
  unfold GenericPopFrame.afterRelevance
  change (machine.threads.threads.mapIdx (fun index thread =>
    if index == machine.threads.activeThread.toNat then
      {thread with topUserRelevantFrame := FrameRelevance.computeTop ⟨frames.push frame⟩ 1}
    else thread))[machine.threads.activeThread.toNat]? = _
  rw [List.getElem?_mapIdx]
  simp [lookup, refreshedThread]

theorem after_relevance_at_active
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K U) (index : Nat) (thread : ThreadRecord)
    (active : machine.threads.activeThread? = some thread) :
    ∃ threadAfter,
      (GenericPopFrame.afterRelevanceAt frames frame machine index).threads.activeThread? = some threadAfter := by
  by_cases same : index = frames.size
  · subst index
    refine ⟨refreshedThread frames frame thread,?_⟩
    simpa only [GenericPopFrame.afterRelevanceAt,↓reduceIte] using after_relevance_active frames frame machine thread active
  · exact ⟨thread,by simp [GenericPopFrame.afterRelevanceAt,same,active]⟩
end DuplicatePrefix.PopActive

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.PopActive.after_relevance_active,
      ``DuplicatePrefix.PopActive.after_relevance_at_active] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError s!"unapproved post-pop active-thread dependency {dependency}"
