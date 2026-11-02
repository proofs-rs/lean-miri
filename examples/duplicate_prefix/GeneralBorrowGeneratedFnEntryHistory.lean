import duplicate_prefix.GeneralBorrowGeneratedFnEntry
namespace DuplicatePrefix.GeneralBorrowGeneratedFnEntryHistory
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestGeneratedTagHistoryData GeneralBorrowGeneratedFnEntry
set_option maxRecDepth 65536
set_option maxHeartbeats 2500000

inductive Event where
  | source (event : GeneralBorrowForestGeneratedTagHistoryData.Event)
  | fnEntry (parent : BorTag) (offset len : Size) (inside : DedupRangeMap LocationState)
      (outside : Permission) (held : Bool) (mode : ChildrenVisitMode)

def step (id : AllocId) (state : Snapshot) : Event → Result
  | .source event => GeneralBorrowForestGeneratedTagHistoryData.step id state event
  | .fnEntry parent offset len inside outside held mode =>
    match operation id state parent offset len inside outside held mode with
    | .error _ => ⟨state,false⟩
    | .ok output => ⟨output.state,output.access.status==.Completed && output.child.outcome==.ok ()⟩

def Applicable (state : Snapshot) : Event → Prop
  | .source event => GeneralBorrowForestGeneratedReadableHistory.Applicable state event
  | .fnEntry parent offset len inside outside held _ => GeneralBorrowGeneratedFnEntry.Applicable state parent offset len inside outside held

def run (id : AllocId) (state : Snapshot) : List Event → Result
  | [] => ⟨state,true⟩
  | event::rest => let next:=step id state event
    if next.completed then run id next.state rest else next

def Schedule (id : AllocId) (state : Snapshot) : List Event → Prop
  | [] => True
  | event::rest => Applicable state event ∧ ((step id state event).completed=true → Schedule id (step id state event).state rest)

theorem step_preserves (id : AllocId) (state : Snapshot) (formed : Formed id ⟨0⟩ state)
    (event : Event) (allowed : Applicable state event) :
    (step id state event).completed=true ∧ Formed id ⟨0⟩ (step id state event).state := by
  cases event with
  | source event =>
    have frames := GeneralBorrowProtectedGeneratedFramesStep.preserves id ⟨0⟩ state formed.frames event allowed
    have readable := GeneralBorrowForestGeneratedReadableHistory.step_formed id state formed.readable event allowed
    have guard := GeneralBorrowForestGeneratedReadablePrepared.authority_guard state event allowed
    have authority := GeneralBorrowForestGeneratedRootAuthority.step_formed id state ⟨formed.frames.cache.sifa,formed.authority⟩ event guard
    exact ⟨frames.1,frames.2,readable,authority.authority,GeneralBorrowForestGeneratedRootEndFrames.step_cover id state formed.covered event guard⟩
  | fnEntry parent offset len inside outside held mode =>
    obtain ⟨output,actual,readOk,childOk,next⟩ := GeneralBorrowGeneratedFnEntry.invoke id state formed parent offset len inside outside held mode allowed
    simpa only [step,actual,readOk,childOk,beq_self_eq_true,Bool.true_and] using And.intro (rfl : true=true) next

theorem preserves (id : AllocId) (state : Snapshot) (formed : Formed id ⟨0⟩ state)
    (events : List Event) (scheduled : Schedule id state events) :
    (run id state events).completed=true ∧ Formed id ⟨0⟩ (run id state events).state := by
  induction events generalizing state with
  | nil => exact ⟨rfl,formed⟩
  | cons event rest ih =>
    have next:=step_preserves id state formed event scheduled.1
    simpa only [run,next.1,↓reduceIte] using ih _ next.2 (scheduled.2 next.1)

theorem schedule_take (id : AllocId) (state : Snapshot) (events : List Event) (scheduled : Schedule id state events) (count : Nat) :
    Schedule id state (events.take count) := by
  induction events generalizing state count with
  | nil => simp only [List.take_nil,Schedule]
  | cons event rest ih =>
    cases count with
    | zero => trivial
    | succ count => exact ⟨scheduled.1,fun completed=>ih _ (scheduled.2 completed) count⟩

theorem initial_formed (id : AllocId) (size : Size) (tracked : Array BorTag) : Formed id ⟨0⟩ (initial id size tracked) :=
  ⟨GeneralBorrowProtectedGeneratedFramesHistory.initial_formed id size tracked,
    GeneralBorrowForestGeneratedReadableHistory.initial_formed id size tracked,
    GeneralBorrowStructuralHistoryRootAuthorityState.allocation BorTag.one size,
    GeneralBorrowForestGeneratedRootEndFrames.initial_cover id size tracked⟩

/-- Actual allocation seed followed by any finite mix of counter-issued
concrete constructors, GC and complete FnEntry leading-Read macros. Every
bounded prefix derives actual completion, physical readability/SIFA/cache,
full LIFO frame metadata and latent original-root authority internally. -/
theorem from_seed (id : AllocId) (size : Size) (tracked : Array BorTag) (events : List Event)
    (scheduled : Schedule id (initial id size tracked) events) (count : Nat) :
    (run id (initial id size tracked) (events.take count)).completed=true ∧
      Formed id ⟨0⟩ (run id (initial id size tracked) (events.take count)).state :=
  preserves id _ (initial_formed id size tracked) _ (schedule_take id _ events scheduled count)
end DuplicatePrefix.GeneralBorrowGeneratedFnEntryHistory
