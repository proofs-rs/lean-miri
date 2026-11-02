import duplicate_prefix.GeneralBorrowProtectedGeneratedFramesStep
namespace DuplicatePrefix.GeneralBorrowProtectedGeneratedFramesHistory
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestGeneratedTagHistoryData GeneralBorrowPhysicalReadableLifo GeneralBorrowProtectedGeneratedFramesStep
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

theorem initial_formed (id : AllocId) (size : Size) (tracked : Array BorTag) :
    Formed id GeneralBorrowFullSharedSeed.root (initial id size tracked) := by
  refine ⟨?_,?_,rfl⟩
  · exact ⟨GeneralBorrowForestGeneratedSifaHistory.initial_formed id size tracked,
      GeneralBorrowForestGeneratedHiddenOperations.seed BorTag.one size⟩
  · exact ⟨by intro row member;simp [initial] at member,by simp [initial],by intro row member;simp [initial] at member,by intro row member;simp [initial] at member⟩

/-- Same source event evaluator and source-guarded schedule: concrete mixed
constructors allocate their tags from the counter and retain singleton frames;
real GC keeps every frame-held tagged node. No per-event metadata, held bits,
cache profile or successful operation is added to the schedule. -/
theorem preserves (id : AllocId) (root : UniIndex) (state : Snapshot) (formed : Formed id root state)
    (events : List Event) (scheduled : GeneralBorrowForestGeneratedReadableHistory.Schedule id state events) :
    (GeneralBorrowForestGeneratedTagHistory.run id state events).completed = true ∧
      Formed id root (GeneralBorrowForestGeneratedTagHistory.run id state events).state := by
  induction events generalizing state with
  | nil => exact ⟨rfl,formed⟩
  | cons event rest ih =>
    have next := GeneralBorrowProtectedGeneratedFramesStep.preserves id root state formed event scheduled.1
    simpa only [GeneralBorrowForestGeneratedTagHistory.run,next.1,↓reduceIte] using ih _ next.2 (scheduled.2 next.1)

/-- Initial rootPointerTag/BorrowTree.new and any permitted finite mixed
concrete constructor/GC prefix form all metadata required by actual LIFO
protector release: singleton frames, duplicate-free held keys, physically
present tagged hidden nodes, and the original singleton root. -/
theorem from_seed (id : AllocId) (size : Size) (tracked : Array BorTag) (events : List Event)
    (scheduled : GeneralBorrowForestGeneratedReadableHistory.Schedule id (initial id size tracked) events) (count : Nat) :
    let after := (GeneralBorrowForestGeneratedTagHistory.run id (initial id size tracked) (events.take count)).state
    Frames id after.tree after.global after.frames ∧ after.tree.roots = #[GeneralBorrowFullSharedSeed.root] := by
  have reached := preserves id GeneralBorrowFullSharedSeed.root (initial id size tracked) (initial_formed id size tracked) _
    (GeneralBorrowForestGeneratedReadableHistory.schedule_take id _ _ scheduled count)
  exact ⟨reached.2.frames,reached.2.roots⟩
end DuplicatePrefix.GeneralBorrowProtectedGeneratedFramesHistory
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedGeneratedFrames").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved source-generated frame metadata dependency {dependency}"
