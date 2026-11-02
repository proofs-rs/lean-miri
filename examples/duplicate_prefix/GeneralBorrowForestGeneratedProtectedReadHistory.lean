import duplicate_prefix.GeneralBorrowForestGeneratedProtectedReadStep
namespace DuplicatePrefix.GeneralBorrowForestGeneratedProtectedReadHistory
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestGeneratedTagHistoryData GeneralBorrowForestGeneratedSifaHistory
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- Raw reached-step guards. Reads and actual captured-frame releases use
slice permissions/activity and Read-compatible protected reservations, never intermediate physical SIFA profiles or outcomes. -/
def Schedule (id : AllocId) (state : Snapshot) : List Event → Prop
  | [] => True
  | event::rest => GeneralBorrowForestGeneratedProtectedReadStep.Applicable state event ∧
      ((step id state event).completed=true→Schedule id (step id state event).state rest)

theorem schedule_base (id : AllocId) (state : Snapshot) (events : List Event) (scheduled : Schedule id state events) :
    GeneralBorrowForestGeneratedTagHistory.Schedule id state events := by
  induction events generalizing state with
  | nil => trivial
  | cons event rest ih => exact ⟨GeneralBorrowForestGeneratedProtectedReadStep.base state event scheduled.1,fun completed=>ih _ (scheduled.2 completed)⟩

/-- Every operation in this selected source family completes from its raw
reached-step guard, and forms the joint invariant for the next actual event. -/
theorem preserves (id : AllocId) (state : Snapshot) (formed : Formed state) (events : List Event)
    (scheduled : Schedule id state events) :
    (GeneralBorrowForestGeneratedTagHistory.run id state events).completed=true ∧
    Formed (GeneralBorrowForestGeneratedTagHistory.run id state events).state := by
  induction events generalizing state with
  | nil => exact ⟨rfl,formed⟩
  | cons event rest ih =>
    have completed := (GeneralBorrowForestGeneratedProtectedReadStep.preserves id state formed event scheduled.1).1
    have next := (GeneralBorrowForestGeneratedProtectedReadStep.preserves id state formed event scheduled.1).2
    simpa only [GeneralBorrowForestGeneratedTagHistory.run,completed,↓reduceIte] using ih _ next (scheduled.2 completed)

theorem schedule_take (id : AllocId) (state : Snapshot) (events : List Event) (scheduled : Schedule id state events) (count : Nat) :
    Schedule id state (events.take count) := by
  induction events generalizing state count with
  | nil => simp only [List.take_nil,Schedule]
  | cons event rest ih =>
    cases count with
    | zero => trivial
    | succ count => exact ⟨scheduled.1,fun completed=>ih _ (scheduled.2 completed) count⟩

/-- Same actual root allocation, counter allocation, optional registration and
captured frames, real constructors, concrete Reads, releases/endCall and GC.
Every permitted finite prefix completes and forms high-water, full allocator,
physical SIFA and vacant Clean, including compatible active held Default reservations. Raw cache coherence is required for the protected-Read alternative. Arbitrary access errors are not treated as safe;
they are outside this permission-guarded protocol. -/
theorem from_seed (id : AllocId) (size : Size) (tracked : Array BorTag) (events : List Event)
    (scheduled : Schedule id (initial id size tracked) events) (count : Nat) :
    seed id size tracked=.ok (initial id size tracked) ∧
    (GeneralBorrowForestGeneratedTagHistory.run id (initial id size tracked) (events.take count)).completed=true ∧
    Formed (GeneralBorrowForestGeneratedTagHistory.run id (initial id size tracked) (events.take count)).state ∧
    (GeneralBorrowForestGeneratedTagHistory.run id (initial id size tracked) (events.take count)).state.tree.locations.size=(BorrowTree.new BorTag.one size).locations.size := by
  have joint := preserves id _ (GeneralBorrowForestGeneratedSifaHistory.initial_formed id size tracked) _ (schedule_take id _ _ scheduled count)
  have generated := GeneralBorrowForestGeneratedTagHistory.from_seed id size tracked events (schedule_base id _ _ scheduled) count
  exact ⟨seed_actual id size tracked,joint.1,joint.2,generated.2.2⟩

theorem full_activity (id : AllocId) (size : Size) (tracked : Array BorTag) (events : List Event)
    (scheduled : Schedule id (initial id size tracked) events) (count : Nat) (index : UniIndex) :
    GeneralBorrowFreshActiveWithin.ActiveWithin
      (GeneralBorrowForestGeneratedTagHistory.run id (initial id size tracked) (events.take count)).state.tree index .Write 0 (BorrowTree.new BorTag.one size).locations.size.bytes := by
  have formed := from_seed id size tracked events scheduled count
  have activity := GeneralBorrowStructuralHistoryActivityFull.full _ index formed.2.2.1.generated.structural.well
  rw [formed.2.2.2] at activity
  exact activity
end DuplicatePrefix.GeneralBorrowForestGeneratedProtectedReadHistory
