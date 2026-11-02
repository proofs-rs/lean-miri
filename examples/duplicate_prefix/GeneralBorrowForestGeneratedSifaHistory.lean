import duplicate_prefix.GeneralBorrowForestGeneratedTagHistory
import duplicate_prefix.GeneralBorrowForestGeneratedTagHistoryFlags
import duplicate_prefix.GeneralBorrowStructuralHistorySifaChronology
import duplicate_prefix.GeneralBorrowStructuralHistoryActivityFull
namespace DuplicatePrefix.GeneralBorrowForestGeneratedSifaHistory
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestGeneratedTagHistoryData GeneralBorrowLocationSifaConsistency GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- Same actual global/tree/frame runtime as generated-tag history. Physical
SIFA formation includes stored vacant-slot Clean. Whole-buffer Write activity
is a geometric confinement fact, not permission to write. -/
structure Formed (state : Snapshot) : Prop where
  generated : Invariant state
  profile : Every (fun location => Profile state.tree location state.global.protectedTags) state.tree.locations

/-- Allocation and optional registration are performed by the existing source
step. The extra guards are scalar inside-policy consistency, never a supplied
fresh tag, protection-alignment flag, intermediate profile or success result.
Access and protector-release protocols require separate permission invariants. -/
def Applicable (state : Snapshot) (event : Event) : Prop :=
  GeneralBorrowForestGeneratedTagHistoryData.Applicable state event ∧ match event with
  | .constructor _ _ inside _ held => ∀segment∈inside.iterAll.toList,GeneralBorrowSifaPermissionConsistency.Consistent segment.data held
  | .allocate | .gc _ => True
  | .access .. | .release => False

private theorem registered_profile (id : AllocId) (state : Snapshot) (formed : Formed state)
    (room : state.global.nextPointerTag.value<18446744073709551615) (held : Bool) :
    let allocated : GlobalState := {state.global with nextPointerTag:=TypedRetagEmpty.successorTag state.global.nextPointerTag room}
    let registered := register id state allocated state.global.nextPointerTag held
    Every (fun location => Profile state.tree location registered.global.protectedTags) state.tree.locations := by
  have fresh := GeneralBorrowForestGeneratedTagHistoryData.fresh state formed.generated
  cases held with
  | false => exact formed.profile
  | true =>
    exact GeneralBorrowSifaProtectionProfile.register state.tree
      {state.global with nextPointerTag:=TypedRetagEmpty.successorTag state.global.nextPointerTag room}
      {} id state.global.nextPointerTag .StrongProtector fresh formed.generated.structural.allocator.nodeTags formed.profile

theorem step_formed (id : AllocId) (state : Snapshot) (formed : Formed state)
    (event : Event) (allowed : Applicable state event) : Formed (step id state event).state := by
  have structural := (GeneralBorrowForestGeneratedTagHistoryStep.preserves id state formed.generated event allowed.1).1
  refine ⟨structural,?_⟩
  cases event with
  | access source offset len kind mode => exact False.elim allowed.2
  | release => exact False.elim allowed.2
  | allocate =>
    have actual := TypedRetagEmpty.allocate_tag state.global allowed.1
    simpa only [step,actual] using formed.profile
  | gc live =>
    exact (GeneralBorrowStructuralHistorySifaState.gc state.tree state.global.protectedTags
      ⟨formed.generated.structural,formed.profile⟩ live).2.profile
  | constructor parent base inside outside held =>
    obtain ⟨room,nodeRoom,parentData,initialOutside,notUnique,⟨sifa,foreign⟩,bounded,insideInitial⟩ := allowed.1
    let allocated : GlobalState := {state.global with nextPointerTag:=TypedRetagEmpty.successorTag state.global.nextPointerTag room}
    let registered := register id state allocated state.global.nextPointerTag held
    have flags := GeneralBorrowForestGeneratedTagHistoryFlags.generated id state formed.generated room held
    have before := registered_profile id state formed room held
    have consistent : ∀segment∈inside.iterAll.toList,GeneralBorrowSifaPermissionConsistency.Consistent segment.data (registered.global.protectedTags.contains state.global.nextPointerTag) := by
      rw [flags.2.1]
      exact allowed.2
    have fresh := GeneralBorrowForestGeneratedTagHistoryData.fresh state formed.generated
    have physical : Every (fun location => Profile (state.tree.newChild base parent state.global.nextPointerTag inside outside held).tree location registered.global.protectedTags)
        (state.tree.newChild base parent state.global.nextPointerTag inside outside held).tree.locations := by
      cases parent with
      | wildcard =>
        exact GeneralBorrowStructuralHistorySifaWildcard.profile state.tree formed.generated.structural registered.global.protectedTags before
          state.global.nextPointerTag fresh nodeRoom outside sifa held initialOutside notUnique foreign flags.2.1 base inside bounded consistent
      | concrete parentTag =>
        obtain ⟨parent,node,tagged,present⟩ := parentData
        exact GeneralBorrowStructuralHistorySifaConcrete.profile state.tree formed.generated.structural registered.global.protectedTags before
          parentTag parent node tagged present state.global.nextPointerTag fresh nodeRoom outside sifa held initialOutside notUnique foreign flags.2.1 base inside bounded consistent
    simpa only [step,flags.1] using physical

/-- The source run stops on its actual failure bit. Every reached prefix
therefore retains the joint global high-water, allocator and physical SIFA
invariant, including the actual error poststate. -/
def Schedule (id : AllocId) (state : Snapshot) : List Event → Prop
  | [] => True
  | event::rest => Applicable state event ∧ ((step id state event).completed=true→Schedule id (step id state event).state rest)

theorem schedule_base (id : AllocId) (state : Snapshot) (events : List Event) (scheduled : Schedule id state events) :
    GeneralBorrowForestGeneratedTagHistory.Schedule id state events := by
  induction events generalizing state with
  | nil => trivial
  | cons event rest ih => exact ⟨scheduled.1.1,fun completed=>ih _ (scheduled.2 completed)⟩

theorem preserves (id : AllocId) (state : Snapshot) (formed : Formed state) (events : List Event)
    (scheduled : Schedule id state events) : Formed (GeneralBorrowForestGeneratedTagHistory.run id state events).state := by
  induction events generalizing state with
  | nil => exact formed
  | cons event rest ih =>
    have next := step_formed id state formed event scheduled.1
    cases completed : (step id state event).completed with
    | false => simpa only [GeneralBorrowForestGeneratedTagHistory.run,completed,Bool.false_eq_true,↓reduceIte] using next
    | true => simpa only [GeneralBorrowForestGeneratedTagHistory.run,completed,↓reduceIte] using ih _ next (scheduled.2 completed)

theorem schedule_take (id : AllocId) (state : Snapshot) (events : List Event) (scheduled : Schedule id state events) (count : Nat) :
    Schedule id state (events.take count) := by
  induction events generalizing state count with
  | nil => simp only [List.take_nil,Schedule]
  | cons event rest ih =>
    cases count with
    | zero => trivial
    | succ count => exact ⟨scheduled.1,fun completed=>ih _ (scheduled.2 completed) count⟩

theorem initial_formed (id : AllocId) (size : Size) (tracked : Array BorTag) : Formed (initial id size tracked) :=
  ⟨initial_invariant id size tracked,(GeneralBorrowStructuralHistorySifaState.initial BorTag.one size _).profile⟩

theorem vacant_clean (state : Snapshot) (formed : Formed state) :
    GeneralBorrowGcVacantClean.VacantClean state.tree :=
  GeneralBorrowStructuralHistorySifaState.vacant_clean state.tree state.global.protectedTags ⟨formed.generated.structural,formed.profile⟩

/-- The joint invariant is formed from the actual rootPointerTag allocation,
then actual counter allocation, optional addProtector/frame capture, concrete or
wildcard constructors, and GC. No initial high-water or SIFA premise is needed. -/
theorem from_seed (id : AllocId) (size : Size) (tracked : Array BorTag) (events : List Event)
    (scheduled : Schedule id (initial id size tracked) events) (count : Nat) :
    seed id size tracked=.ok (initial id size tracked) ∧
    Formed (GeneralBorrowForestGeneratedTagHistory.run id (initial id size tracked) (events.take count)).state ∧
    (GeneralBorrowForestGeneratedTagHistory.run id (initial id size tracked) (events.take count)).state.tree.locations.size=(BorrowTree.new BorTag.one size).locations.size := by
  have joint := preserves id _ (initial_formed id size tracked) _ (schedule_take id _ _ scheduled count)
  have generated := GeneralBorrowForestGeneratedTagHistory.from_seed id size tracked events (schedule_base id _ _ scheduled) count
  exact ⟨seed_actual id size tracked,joint,generated.2.2⟩

theorem full_activity (id : AllocId) (size : Size) (tracked : Array BorTag) (events : List Event)
    (scheduled : Schedule id (initial id size tracked) events) (count : Nat) (index : UniIndex) :
    GeneralBorrowFreshActiveWithin.ActiveWithin
      (GeneralBorrowForestGeneratedTagHistory.run id (initial id size tracked) (events.take count)).state.tree index .Write 0 (BorrowTree.new BorTag.one size).locations.size.bytes := by
  have formed := from_seed id size tracked events scheduled count
  have activity := GeneralBorrowStructuralHistoryActivityFull.full _ index formed.2.1.generated.structural.well
  rw [formed.2.2] at activity
  exact activity
end DuplicatePrefix.GeneralBorrowForestGeneratedSifaHistory
