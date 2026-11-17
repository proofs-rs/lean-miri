import duplicate_prefix.GeneralBorrowStructuralHistoryMutable
import duplicate_prefix.GeneralBorrowStructuralHistoryFrames
namespace DuplicatePrefix.GeneralBorrowStructuralHistory
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowStructuralHistoryState
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- Source permission/allocator operations. A child event is a protected Default
reservation; access events include both kinds and concrete/wildcard sources. -/
inductive Event where
  | access (source : ProvenanceExtra) (offset len : Size) (kind : AccessKind) (protections : ProtectedTags) (mode : ChildrenVisitMode)
  | child (parentTag newTag : BorTag) (offset len : UInt64)
  | expose (tag : BorTag) (protections : ProtectedTags)
  | release (tag : BorTag) (protections : ProtectedTags)
  | gc (live : Array BorTag)

structure Result where
  tree : BorrowTree
  completed : Bool

/-- Raw event applicability. Graph validity and operation outcomes are not
assumptions: only original stored lookups, freshness, bounds and numeric room. -/
def Applicable (tree : BorrowTree) : Event → Prop
  | .access _ offset len .. => offset.bytes.toNat+len.bytes.toNat≤tree.locations.size.bytes.toNat
  | .child parentTag newTag offset len =>
      (∃parent node,tree.indexOfTag parentTag=some parent ∧ tree.nodeAt parent=some node) ∧
      GeneralBorrowTagMap.Fresh tree.tagMapping newTag ∧ tree.nodes.size+1≤4294967295 ∧ len≠0 ∧
      offset.toNat+len.toNat≤tree.locations.size.bytes.toNat
  | .expose .. | .release .. | .gc .. => True

def step (tree : BorrowTree) : Event → Result
  | .access source offset len kind protections mode =>
      let actual := tree.performBorrowAccessRange source offset len kind protections mode
      ⟨actual.tree,actual.status == .Completed⟩
  | .child parentTag newTag offset len =>
      let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
        (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
      ⟨actual.tree,actual.outcome == .ok ()⟩
  | .expose tag protections =>
      let actual := tree.exposeTag protections tag
      ⟨actual.tree,actual.outcome == .ok ()⟩
  | .release tag protections =>
      let actual := tree.releaseProtector tag protections
      ⟨actual.tree,actual.status == .Released⟩
  | .gc live =>
      let actual := tree.removeUnreachableTags live
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
  | access source offset len kind protections mode => exact GeneralBorrowStructuralHistoryFrames.access tree initial source offset len kind protections mode allowed
  | expose tag protections => exact GeneralBorrowStructuralHistoryFrames.expose tree initial tag protections
  | release tag protections => exact GeneralBorrowStructuralHistoryFrames.release tree initial tag protections
  | gc live =>
    have checked := GeneralBorrowStructuralHistoryState.gc tree initial live
    exact ⟨checked.2.1,checked.2.2⟩
  | child parentTag newTag offset len =>
    obtain ⟨⟨parent,node,tagged,present⟩,fresh,room,nonzero,bounds⟩ := allowed
    have checked := GeneralBorrowStructuralHistoryMutable.construct tree initial parentTag newTag parent node tagged present fresh room offset len nonzero bounds
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
end DuplicatePrefix.GeneralBorrowStructuralHistory
