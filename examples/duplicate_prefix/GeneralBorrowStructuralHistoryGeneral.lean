import duplicate_prefix.GeneralBorrowStructuralHistoryMixed
import duplicate_prefix.GeneralBorrowStructuralHistoryMixedConcrete
namespace DuplicatePrefix.GeneralBorrowStructuralHistoryGeneral
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowStructuralHistoryState
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- General concrete and wildcard newChild maps join the checked source-operation
history. The theorem concerns structure; permission validity and Rust UB freedom
are separate obligations. -/
inductive Event where
  | previous (event : GeneralBorrowStructuralHistoryMixed.Event)
  | concrete (parentTag tag : BorTag) (base : Size) (inside : DedupRangeMap LocationState) (outside : Permission) (held : Bool)

abbrev Result := GeneralBorrowStructuralHistory.Result

def Applicable (tree : BorrowTree) : Event → Prop
  | .previous event => GeneralBorrowStructuralHistoryMixed.Applicable tree event
  | .concrete parentTag tag base inside outside held =>
      (∃parent node,tree.indexOfTag parentTag=some parent ∧ tree.nodeAt parent=some node) ∧
      GeneralBorrowTagMap.Fresh tree.tagMapping tag ∧ tree.nodes.size+1≤4294967295 ∧
      outside.isInitial=true ∧ outside.isUnique=false ∧
      (∃sifa,outside.strongestIdempotentForeignAccess held=.Access sifa) ∧
      GeneralBorrowStructuralHistoryMixedConcrete.Bounded inside base tree.locations.size

def step (tree : BorrowTree) : Event → Result
  | .previous event => GeneralBorrowStructuralHistoryMixed.step tree event
  | .concrete parentTag tag base inside outside held =>
      let actual := tree.newChild base (.concrete parentTag) tag inside outside held
      ⟨actual.tree,actual.outcome == .ok ()⟩

/-- Actual operations stop at the first failure, retaining its real partial
poststate. An unsuccessful operation never becomes a successful no-op. -/
def run (tree : BorrowTree) : List Event → Result
  | [] => ⟨tree,true⟩
  | event::rest =>
      let actual := step tree event
      if actual.completed then run actual.tree rest else actual

/-- Every reached event satisfies only its raw applicability guard. No
intermediate State or successful outcome is a field of the schedule. -/
def Schedule (tree : BorrowTree) : List Event → Prop
  | [] => True
  | event::rest => Applicable tree event ∧
      ((step tree event).completed=true → Schedule (step tree event).tree rest)

theorem step_preserves (tree : BorrowTree) (initial : State tree) (event : Event) (allowed : Applicable tree event) :
    State (step tree event).tree ∧ (step tree event).tree.locations.size=tree.locations.size := by
  cases event with
  | previous event => exact GeneralBorrowStructuralHistoryMixed.step_preserves tree initial event allowed
  | concrete parentTag tag base inside outside held =>
    obtain ⟨⟨parent,node,tagged,present⟩,fresh,room,initialOutside,notUnique,⟨sifa,foreign⟩,bounded⟩ := allowed
    have checked := GeneralBorrowStructuralHistoryMixedConcrete.preserves tree initial parentTag parent node tagged present tag fresh room outside sifa held initialOutside notUnique foreign base inside bounded
    exact ⟨checked.1,checked.2.1⟩

/-- Arbitrary finite source-operation histories retain complete intrinsic
structure, also when they stop in an access/release/error partial poststate.
Permission-operation success and Rust UB freedom are separate claims. -/
theorem preserves (tree : BorrowTree) (initial : State tree) (events : List Event) (scheduled : Schedule tree events) :
    State (run tree events).tree ∧ (run tree events).tree.locations.size=tree.locations.size := by
  induction events generalizing tree with
  | nil => exact ⟨initial,rfl⟩
  | cons event rest ih =>
    have head := step_preserves tree initial event scheduled.1
    cases completed : (step tree event).completed with
    | false => simpa only [run,completed,Bool.false_eq_true,↓reduceIte] using head
    | true =>
      have tail := ih (step tree event).tree head.1 (scheduled.2 completed)
      simpa only [run,completed,↓reduceIte] using And.intro tail.1 (tail.2.trans head.2)

theorem schedule_take (tree : BorrowTree) (events : List Event) (scheduled : Schedule tree events) (count : Nat) :
    Schedule tree (events.take count) := by
  induction events generalizing tree count with
  | nil => simp only [List.take_nil,Schedule]
  | cons event rest ih =>
    cases count with
    | zero => trivial
    | succ count => exact ⟨scheduled.1,fun completed => ih _ (scheduled.2 completed) count⟩

/-- Public formation theorem begins with the genuine allocation constructor.
Every permitted finite prefix, on success or failure, has reciprocal finite
forest/parent/root certificates, coherent sparse allocator, bounded capacity
and a well-formed partition with the original byte size. -/
theorem from_new (tag : BorTag) (size : Size) (events : List Event)
    (scheduled : Schedule (BorrowTree.new tag size) events) (count : Nat) :
    State (run (BorrowTree.new tag size) (events.take count)).tree ∧
    (run (BorrowTree.new tag size) (events.take count)).tree.locations.size=(BorrowTree.new tag size).locations.size :=
  preserves _ (GeneralBorrowStructuralHistorySeed.initial tag size) _ (schedule_take _ _ scheduled count)
end DuplicatePrefix.GeneralBorrowStructuralHistoryGeneral
