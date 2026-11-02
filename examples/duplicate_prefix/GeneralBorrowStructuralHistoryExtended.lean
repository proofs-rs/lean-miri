import duplicate_prefix.GeneralBorrowStructuralHistory
import duplicate_prefix.GeneralBorrowStructuralHistoryDefault
import duplicate_prefix.GeneralBorrowStructuralHistoryShared
import duplicate_prefix.GeneralBorrowStructuralHistoryWildcard
namespace DuplicatePrefix.GeneralBorrowStructuralHistoryExtended
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowStructuralHistoryState
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- The typed homogeneous structural protocol extends the checked base history
with unprotected Default, Frozen shared and parentless wildcard constructors.
This is not the full Rust retag language for arbitrary mixed inside maps. -/
inductive Event where
  | base (event : GeneralBorrowStructuralHistory.Event)
  | default (parentTag newTag : BorTag) (offset len : UInt64)
  | shared (parentTag newTag : BorTag) (held : Bool) (offset len : UInt64)
  | wildcardReservation (newTag : BorTag) (offset len : UInt64)
  | wildcardShared (newTag : BorTag) (held : Bool) (offset len : UInt64)

abbrev Result := GeneralBorrowStructuralHistory.Result

def Applicable (tree : BorrowTree) : Event → Prop
  | .base event => GeneralBorrowStructuralHistory.Applicable tree event
  | .default parentTag newTag offset len | .shared parentTag newTag _ offset len =>
      GeneralBorrowStructuralHistory.Applicable tree (.child parentTag newTag offset len)
  | .wildcardReservation newTag offset len | .wildcardShared newTag _ offset len =>
      GeneralBorrowTagMap.Fresh tree.tagMapping newTag ∧ tree.nodes.size+1≤4294967295 ∧
      offset.toNat+len.toNat≤tree.locations.size.bytes.toNat

def step (tree : BorrowTree) : Event → Result
  | .base event => GeneralBorrowStructuralHistory.step tree event
  | .default parentTag newTag offset len =>
      let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
        (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false
      ⟨actual.tree,actual.outcome == .ok ()⟩
  | .shared parentTag newTag held offset len =>
      let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
        (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen held
      ⟨actual.tree,actual.outcome == .ok ()⟩
  | .wildcardReservation newTag offset len =>
      let actual := tree.newChild (Size.ofBytes offset) .wildcard newTag
        (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
      ⟨actual.tree,actual.outcome == .ok ()⟩
  | .wildcardShared newTag held offset len =>
      let actual := tree.newChild (Size.ofBytes offset) .wildcard newTag
        (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen held
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
  | base event => exact GeneralBorrowStructuralHistory.step_preserves tree initial event allowed
  | default parentTag newTag offset len =>
    obtain ⟨⟨parent,node,tagged,present⟩,fresh,room,nonzero,bounds⟩ := allowed
    have checked := GeneralBorrowStructuralHistoryDefault.construct tree initial parentTag newTag parent node tagged present fresh room offset len nonzero bounds
    exact ⟨checked.2.1,checked.2.2.1⟩
  | shared parentTag newTag held offset len =>
    obtain ⟨⟨parent,node,tagged,present⟩,fresh,room,nonzero,bounds⟩ := allowed
    have checked := GeneralBorrowStructuralHistoryShared.construct tree initial parentTag newTag parent node tagged present fresh room held offset len nonzero bounds
    exact ⟨checked.2.1,checked.2.2.1⟩
  | wildcardReservation newTag offset len =>
    obtain ⟨fresh,room,bounds⟩ := allowed
    have checked := GeneralBorrowStructuralHistoryWildcard.construct tree initial newTag fresh room offset len bounds
    exact ⟨checked.2.1,checked.2.2.1⟩
  | wildcardShared newTag held offset len =>
    obtain ⟨fresh,room,bounds⟩ := allowed
    have checked := GeneralBorrowStructuralHistoryWildcard.shared tree initial newTag fresh room held offset len bounds
    exact ⟨checked.2.1,checked.2.2.1⟩

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
end DuplicatePrefix.GeneralBorrowStructuralHistoryExtended
