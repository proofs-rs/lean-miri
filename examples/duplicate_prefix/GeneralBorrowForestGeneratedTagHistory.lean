import duplicate_prefix.GeneralBorrowForestGeneratedTagHistoryStep
namespace DuplicatePrefix.GeneralBorrowForestGeneratedTagHistory
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestGeneratedTagHistoryData
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- A genuine source failure terminates the generated sequence with its actual
partial tree/global/frame state and false completion flag. -/
def run (id : AllocId) (state : Snapshot) : List Event → Result
  | [] => ⟨state,true⟩
  | event::rest =>
      let actual := step id state event
      if actual.completed then run id actual.state rest else actual

/-- Reached runtime numeric/parent/inside/protection guards only. In particular
no initial high-water invariant, Fresh tag, intermediate Invariant or source
success condition is a field. Constructor tags are source-generated counters. -/
def Schedule (id : AllocId) (state : Snapshot) : List Event → Prop
  | [] => True
  | event::rest => Applicable state event ∧
      ((step id state event).completed=true → Schedule id (step id state event).state rest)

theorem preserves (id : AllocId) (state : Snapshot) (initial : Invariant state) (events : List Event)
    (scheduled : Schedule id state events) :
    Invariant (run id state events).state ∧ (run id state events).state.tree.locations.size=state.tree.locations.size := by
  induction events generalizing state with
  | nil => exact ⟨initial,rfl⟩
  | cons event rest ih =>
    have head := GeneralBorrowForestGeneratedTagHistoryStep.preserves id state initial event scheduled.1
    cases completed : (step id state event).completed with
    | false => simpa only [run,completed,Bool.false_eq_true,↓reduceIte] using head
    | true =>
      have tail := ih (step id state event).state head.1 (scheduled.2 completed)
      simpa only [run,completed,↓reduceIte] using And.intro tail.1 (tail.2.trans head.2)

theorem schedule_take (id : AllocId) (state : Snapshot) (events : List Event)
    (scheduled : Schedule id state events) (count : Nat) : Schedule id state (events.take count) := by
  induction events generalizing state count with
  | nil => simp only [List.take_nil,Schedule]
  | cons event rest ih =>
    cases count with
    | zero => trivial
    | succ count => exact ⟨scheduled.1,fun completed => ih _ (scheduled.2 completed) count⟩

/-- Raw global high-water is FORMED inductively from actual GlobalState.new,
rootPointerTag and BorrowTree.new, through real fresh allocation/register,
mixed concrete/wildcard constructors, accesses, stored-frame releases and GC.
Every permitted finite prefix is covered. Access/release error prefixes retain
false completion; this is a tag/structural formation theorem, not a Rust-wide
UB-freedom assertion or an assertion that those source errors succeed. -/
theorem from_seed (id : AllocId) (size : Size) (tracked : Array BorTag) (events : List Event)
    (scheduled : Schedule id (initial id size tracked) events) (count : Nat) :
    seed id size tracked=.ok (initial id size tracked) ∧
      Invariant (run id (initial id size tracked) (events.take count)).state ∧
      (run id (initial id size tracked) (events.take count)).state.tree.locations.size=(BorrowTree.new BorTag.one size).locations.size := by
  have formed := preserves id (initial id size tracked) (initial_invariant id size tracked) _
    (schedule_take id _ events scheduled count)
  exact ⟨seed_actual id size tracked,formed.1,formed.2⟩

theorem fresh_after_prefix (id : AllocId) (size : Size) (tracked : Array BorTag) (events : List Event)
    (scheduled : Schedule id (initial id size tracked) events) (count : Nat) :
    let current := (run id (initial id size tracked) (events.take count)).state
    GeneralBorrowTagMap.Fresh current.tree.tagMapping current.global.nextPointerTag :=
  GeneralBorrowForestGeneratedTagHistoryData.fresh _ (from_seed id size tracked events scheduled count).2.1
end DuplicatePrefix.GeneralBorrowForestGeneratedTagHistory
