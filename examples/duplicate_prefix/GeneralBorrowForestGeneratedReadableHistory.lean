import duplicate_prefix.GeneralBorrowForestGeneratedSifaHistory
import duplicate_prefix.GeneralBorrowStructuralHistoryReadableConcrete
import duplicate_prefix.GeneralBorrowPhysicalReadableProtections
import duplicate_prefix.GeneralBorrowPhysicalReadableSeed
import duplicate_prefix.GeneralBorrowPhysicalReadableGc
namespace DuplicatePrefix.GeneralBorrowForestGeneratedReadableHistory
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestGeneratedTagHistoryData GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- Joint physical readability is formed by the same counter-issued source
constructors, optional protector registration and real GC as the runtime. -/
structure Formed (state : Snapshot) : Prop where
  sifa : GeneralBorrowForestGeneratedSifaHistory.Formed state
  readable : Every (fun location=>GeneralBorrowPhysicalReadable.Profile state.tree location state.global.protectedTags) state.tree.locations

/-- Initial source policy checks, concrete Default/Frozen outside policy and
readable inside permissions. No intermediate ownership, readable profile or
successful operation is supplied as a reached-step guard. -/
def Applicable (state : Snapshot) (event : Event) : Prop :=
  GeneralBorrowForestGeneratedSifaHistory.Applicable state event ∧ match event with
  | .constructor (.concrete _) _ inside outside held =>
    (outside=.ReservedFrz false ∨ outside=.Frozen) ∧
      ∀segment∈inside.iterAll.toList,GeneralBorrowProtectedReadInvariant.Readable segment.data held
  | .constructor .wildcard .. => False
  | _ => True

private theorem registered_readable (id : AllocId) (state : Snapshot) (formed : Formed state)
    (room : state.global.nextPointerTag.value<18446744073709551615) (held : Bool) :
    let allocated : GlobalState := {state.global with nextPointerTag:=TypedRetagEmpty.successorTag state.global.nextPointerTag room}
    let registered := register id state allocated state.global.nextPointerTag held
    Every (fun location=>GeneralBorrowPhysicalReadable.Profile state.tree location registered.global.protectedTags) state.tree.locations := by
  have fresh := GeneralBorrowForestGeneratedTagHistoryData.fresh state formed.sifa.generated
  cases held with
  | false => exact formed.readable
  | true =>
    exact GeneralBorrowPhysicalReadableProtections.register state.tree
      {state.global with nextPointerTag:=TypedRetagEmpty.successorTag state.global.nextPointerTag room}
      {} id state.global.nextPointerTag .StrongProtector fresh formed.sifa.generated.structural.allocator.nodeTags formed.readable

theorem step_formed (id : AllocId) (state : Snapshot) (formed : Formed state) (event : Event)
    (allowed : Applicable state event) : Formed (step id state event).state := by
  have nextSifa := GeneralBorrowForestGeneratedSifaHistory.step_formed id state formed.sifa event allowed.1
  refine ⟨nextSifa,?_⟩
  cases event with
  | access source offset len kind mode => exact False.elim allowed.1.2
  | release => exact False.elim allowed.1.2
  | allocate =>
    have actual := TypedRetagEmpty.allocate_tag state.global allowed.1.1
    simpa only [step,actual] using formed.readable
  | gc live => exact GeneralBorrowPhysicalReadableGc.collect state.tree state.global.protectedTags live formed.readable
  | constructor parent base inside outside held =>
    cases parent with
    | wildcard => exact False.elim allowed.2
    | concrete parentTag =>
      obtain ⟨room,nodeRoom,parentData,initialOutside,notUnique,⟨sifa,foreign⟩,bounded,insideInitial⟩ := allowed.1.1
      obtain ⟨parent,node,tagged,present⟩ := parentData
      have flags := GeneralBorrowForestGeneratedTagHistoryFlags.generated id state formed.sifa.generated room held
      have fresh := GeneralBorrowForestGeneratedTagHistoryData.fresh state formed.sifa.generated
      let allocated : GlobalState := {state.global with nextPointerTag:=TypedRetagEmpty.successorTag state.global.nextPointerTag room}
      let registered := register id state allocated state.global.nextPointerTag held
      have before := registered_readable id state formed room held
      have defaultReadable : GeneralBorrowProtectedReadInvariant.Readable ⟨outside,false,sifa⟩ held := by
        rcases allowed.2.1 with rfl | rfl <;>
          cases held <;> simp [GeneralBorrowProtectedReadInvariant.Readable,LocationState.possible,Permission.isUnique]
      have insideReadable : ∀segment∈inside.iterAll.toList,
          GeneralBorrowProtectedReadInvariant.Readable segment.data (registered.global.protectedTags.contains state.global.nextPointerTag) := by
        rw [flags.2.1]
        exact allowed.2.2
      have physical := GeneralBorrowStructuralHistoryReadableConcrete.profile state.tree formed.sifa.generated.structural registered.global.protectedTags before
        parentTag parent node tagged present state.global.nextPointerTag fresh nodeRoom outside sifa held initialOutside notUnique foreign flags.2.1
        base inside bounded defaultReadable insideReadable
      simpa only [step,flags.1] using physical

def Schedule (id : AllocId) (state : Snapshot) : List Event→Prop
  | [] => True
  | event::rest => Applicable state event ∧ ((step id state event).completed=true→Schedule id (step id state event).state rest)

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
  ⟨GeneralBorrowForestGeneratedSifaHistory.initial_formed id size tracked,
    GeneralBorrowPhysicalReadableSeed.allocation size.bytes BorTag.one {} (by simp [ProtectedTags.contains,ProtectedTags.get])⟩

/-- Seed allocation and arbitrary permitted generated constructor/GC prefixes
form the complete per-present-node Readable profile; no final profile or
current root Write ownership is an assumption. -/
theorem from_seed (id : AllocId) (size : Size) (tracked : Array BorTag) (events : List Event)
    (scheduled : Schedule id (initial id size tracked) events) (count : Nat) :
    Formed (GeneralBorrowForestGeneratedTagHistory.run id (initial id size tracked) (events.take count)).state :=
  preserves id _ (initial_formed id size tracked) _ (schedule_take id _ events scheduled count)
end DuplicatePrefix.GeneralBorrowForestGeneratedReadableHistory
