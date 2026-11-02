import duplicate_prefix.GeneralBorrowStructuralHistorySifaConcrete
import duplicate_prefix.GeneralBorrowStructuralHistorySifaWildcard
import duplicate_prefix.GeneralBorrowSifaProtectionProfile
namespace DuplicatePrefix.GeneralBorrowStructuralHistorySifaChronology
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowStructuralHistoryState GeneralBorrowStructuralHistorySifaState GeneralBorrowLocationSifaConsistency GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

structure Runtime where
  tree : BorrowTree
  global : GlobalState
  frame : FrameState

/-- Constructor/registration/GC chronology. This is the source borrow-tracker
protocol; arbitrary Rust callers and tree protector-release accesses are separate. -/
inductive Event where
  | concrete (parentTag tag : BorTag) (base : Size) (inside : DedupRangeMap LocationState) (outside : Permission) (held : Bool)
  | wildcard (tag : BorTag) (base : Size) (inside : DedupRangeMap LocationState) (outside : Permission) (held : Bool)
  | register (allocation : AllocId) (tag : BorTag) (kind : ProtectorKind)
  | gc (live : Array BorTag)

structure Result where
  runtime : Runtime
  completed : Bool

def Formed (state : Runtime) : Prop := GeneralBorrowStructuralHistorySifaState.Formed state.tree state.global.protectedTags

def ConstructorData (state : Runtime) (tag : BorTag) (base : Size) (inside : DedupRangeMap LocationState) (outside : Permission) (held : Bool) : Prop :=
  GeneralBorrowTagMap.Fresh state.tree.tagMapping tag ∧ state.tree.nodes.size+1≤4294967295 ∧
  outside.isInitial=true ∧ outside.isUnique=false ∧
  (∃sifa,outside.strongestIdempotentForeignAccess held=.Access sifa) ∧
  state.global.protectedTags.contains tag=held ∧
  GeneralBorrowStructuralHistoryMixedWildcard.Bounded inside base state.tree.locations.size ∧
  (∀segment∈inside.iterAll.toList,GeneralBorrowSifaPermissionConsistency.Consistent segment.data (state.global.protectedTags.contains tag))

/-- Only raw stored lookups, numeric bounds and requested initial-policy scalar
checks are guards. No intermediate physical Profile or operation outcome is supplied. -/
def Applicable (state : Runtime) : Event → Prop
  | .concrete parentTag tag base inside outside held =>
      (∃parent node,state.tree.indexOfTag parentTag=some parent ∧ state.tree.nodeAt parent=some node) ∧ ConstructorData state tag base inside outside held
  | .wildcard tag base inside outside held => ConstructorData state tag base inside outside held
  | .register _ tag _ => GeneralBorrowTagMap.Fresh state.tree.tagMapping tag
  | .gc _ => True

def step (state : Runtime) : Event → Result
  | .concrete parentTag tag base inside outside held =>
      let actual:=state.tree.newChild base (.concrete parentTag) tag inside outside held
      ⟨{state with tree:=actual.tree},actual.outcome == .ok ()⟩
  | .wildcard tag base inside outside held =>
      let actual:=state.tree.newChild base .wildcard tag inside outside held
      ⟨{state with tree:=actual.tree},actual.outcome == .ok ()⟩
  | .register allocation tag kind =>
      let actual:=state.global.addProtector state.frame allocation tag kind
      ⟨{state with global:=actual.1,frame:=actual.2},true⟩
  | .gc live =>
      let actual:=state.tree.removeUnreachableTags live
      ⟨{state with tree:=actual.tree},actual.outcome == .ok ()⟩

def run (state : Runtime) : List Event → Result
  | [] => ⟨state,true⟩
  | event::rest => let actual:=step state event; if actual.completed then run actual.runtime rest else actual

def Schedule (state : Runtime) : List Event → Prop
  | [] => True
  | event::rest => Applicable state event ∧ ((step state event).completed=true→Schedule (step state event).runtime rest)

theorem step_formed (state : Runtime) (initial : Formed state) (event : Event) (allowed : Applicable state event) :
    Formed (step state event).runtime := by
  cases event with
  | register allocation tag kind =>
    exact ⟨initial.toState,GeneralBorrowSifaProtectionProfile.register state.tree state.global state.frame allocation tag kind allowed
      initial.allocator.nodeTags initial.profile⟩
  | gc live => exact (GeneralBorrowStructuralHistorySifaState.gc state.tree state.global.protectedTags initial live).2
  | wildcard tag base inside outside held =>
    obtain ⟨fresh,room,initialOutside,notUnique,⟨sifa,foreign⟩,aligned,bounded,consistent⟩ := allowed
    have structural := GeneralBorrowStructuralHistoryMixedWildcard.preserves state.tree initial.toState tag fresh room outside sifa held initialOutside notUnique foreign base inside bounded
    have physical := GeneralBorrowStructuralHistorySifaWildcard.profile state.tree initial.toState state.global.protectedTags initial.profile tag fresh room outside sifa held initialOutside notUnique foreign aligned base inside bounded consistent
    exact ⟨structural.1,physical⟩
  | concrete parentTag tag base inside outside held =>
    obtain ⟨⟨parent,node,tagged,present⟩,fresh,room,initialOutside,notUnique,⟨sifa,foreign⟩,aligned,bounded,consistent⟩ := allowed
    have structural := GeneralBorrowStructuralHistoryMixedConcrete.preserves state.tree initial.toState parentTag parent node tagged present tag fresh room outside sifa held initialOutside notUnique foreign base inside bounded
    have physical := GeneralBorrowStructuralHistorySifaConcrete.profile state.tree initial.toState state.global.protectedTags initial.profile parentTag parent node tagged present tag fresh room outside sifa held initialOutside notUnique foreign aligned base inside bounded consistent
    exact ⟨structural.1,physical⟩

theorem formed (state : Runtime) (initial : Formed state) (events : List Event) (scheduled : Schedule state events) :
    Formed (run state events).runtime := by
  induction events generalizing state with
  | nil => exact initial
  | cons event rest ih =>
    have next:=step_formed state initial event scheduled.1
    cases completed : (step state event).completed with
    | false => simpa only [run,completed,Bool.false_eq_true,↓reduceIte] using next
    | true => simpa only [run,completed,↓reduceIte] using ih _ next (scheduled.2 completed)

theorem schedule_take (state : Runtime) (events : List Event) (scheduled : Schedule state events) (count : Nat) : Schedule state (events.take count) := by
  induction events generalizing state count with
  | nil => simp only [List.take_nil,Schedule]
  | cons event rest ih =>
    cases count with
    | zero => trivial
    | succ count => exact ⟨scheduled.1,fun completed=>ih _ (scheduled.2 completed) count⟩

/-- Every reached finite prefix forms physical permission/SIFA bounds and
all vacant-slot Clean from allocation, actual registration, arbitrary mixed-map
concrete/wildcard constructors and GC. Initial/final profile and success are
not hypotheses, including when a constructor ends in its real error poststate. -/
theorem from_new (rootTag : BorTag) (size : Size) (global : GlobalState) (frame : FrameState) (events : List Event)
    (scheduled : Schedule ⟨BorrowTree.new rootTag size,global,frame⟩ events) (count : Nat) :
    Formed (run ⟨BorrowTree.new rootTag size,global,frame⟩ (events.take count)).runtime :=
  formed ⟨BorrowTree.new rootTag size,global,frame⟩ (GeneralBorrowStructuralHistorySifaState.initial rootTag size global.protectedTags) _ (schedule_take _ _ scheduled count)
end DuplicatePrefix.GeneralBorrowStructuralHistorySifaChronology
