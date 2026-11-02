import duplicate_prefix.GeneralBorrowForestGeneratedSifaHistory
import duplicate_prefix.GeneralBorrowStructuralHistoryRootAuthorityConcrete
import duplicate_prefix.GeneralBorrowStructuralHistoryRootAuthorityWildcard
namespace DuplicatePrefix.GeneralBorrowForestGeneratedRootAuthority
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestGeneratedTagHistoryData GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- One actual generated-counter runtime carries high-water/structure, physical
SIFA/Clean and latent owning-root authority. Current held child protectors are
not silently treated as absent or compatible with an actual root Write. -/
structure Formed (state : Snapshot) : Prop where
  sifa : GeneralBorrowForestGeneratedSifaHistory.Formed state
  authority : GeneralBorrowStructuralHistoryRootAuthorityState.Formed state.tree ⟨0⟩

/-- Source constructor policy guards plus possible requested inside states.
Counter freshness/protection flags and intermediate authority are all derived.
Access/protector-release protocols require their own preservation proof. -/
def Applicable (state : Snapshot) (event : Event) : Prop :=
  GeneralBorrowForestGeneratedSifaHistory.Applicable state event ∧ match event with
  | .constructor _ _ inside _ _ => ∀segment∈inside.iterAll.toList,segment.data.possible=true
  | _ => True

theorem step_formed (id : AllocId) (state : Snapshot) (formed : Formed state) (event : Event) (allowed : Applicable state event) :
    Formed (step id state event).state := by
  have nextSifa:=GeneralBorrowForestGeneratedSifaHistory.step_formed id state formed.sifa event allowed.1
  refine ⟨nextSifa,?_⟩
  cases event with
  | access source offset len kind mode => exact False.elim allowed.1.2
  | release => exact False.elim allowed.1.2
  | allocate =>
    have actual:=TypedRetagEmpty.allocate_tag state.global allowed.1.1
    simpa only [step,actual] using formed.authority
  | gc live => exact (GeneralBorrowStructuralHistoryRootAuthorityState.gc state.tree ⟨0⟩ formed.authority live).2
  | constructor parent base inside outside held =>
    obtain ⟨room,nodeRoom,parentData,initialOutside,notUnique,⟨sifa,foreign⟩,bounded,insideInitial⟩:=allowed.1.1
    have flags:=GeneralBorrowForestGeneratedTagHistoryFlags.generated id state formed.sifa.generated room held
    have fresh:=GeneralBorrowForestGeneratedTagHistoryData.fresh state formed.sifa.generated
    have authority : (⟨0⟩:UniIndex)∈(step id state (.constructor parent base inside outside held)).state.tree.roots.toList ∧
        GeneralBorrowStructuralHistoryRootAuthorityAt.Profile (step id state (.constructor parent base inside outside held)).state.tree ⟨0⟩ := by
      cases parent with
      | wildcard =>
        have data:=GeneralBorrowStructuralHistoryRootAuthorityWildcard.profile state.tree formed.authority.toState ⟨0⟩ formed.authority.member formed.authority.policy
          state.global.nextPointerTag fresh nodeRoom outside sifa held initialOutside notUnique foreign base inside bounded allowed.2
        simpa only [step,flags.1] using data
      | concrete parentTag =>
        obtain ⟨parent,node,tagged,present⟩:=parentData
        have data:=GeneralBorrowStructuralHistoryRootAuthorityConcrete.profile state.tree formed.authority.toState ⟨0⟩ formed.authority.member formed.authority.policy
          parentTag parent node tagged present state.global.nextPointerTag fresh nodeRoom outside sifa held initialOutside notUnique foreign base inside bounded allowed.2
        simpa only [step,flags.1] using data
    exact ⟨nextSifa.generated.structural,authority.1,authority.2⟩

def Schedule (id : AllocId) (state : Snapshot) : List Event→Prop
  | [] => True
  | event::rest => Applicable state event ∧ ((step id state event).completed=true→Schedule id (step id state event).state rest)

theorem preserves (id : AllocId) (state : Snapshot) (formed : Formed state) (events : List Event) (scheduled : Schedule id state events) :
    Formed (GeneralBorrowForestGeneratedTagHistory.run id state events).state := by
  induction events generalizing state with
  | nil => exact formed
  | cons event rest ih =>
    have next:=step_formed id state formed event scheduled.1
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
  ⟨GeneralBorrowForestGeneratedSifaHistory.initial_formed id size tracked,GeneralBorrowStructuralHistoryRootAuthorityState.allocation BorTag.one size⟩

/-- Actual original allocation and actual counter-issued constructor tags form
latent root authority at every reached finite prefix; no initial/final owner,
fresh tag, selected-slot Clean or operation-success certificate is supplied. -/
theorem from_seed (id : AllocId) (size : Size) (tracked : Array BorTag) (events : List Event)
    (scheduled : Schedule id (initial id size tracked) events) (count : Nat) :
    Formed (GeneralBorrowForestGeneratedTagHistory.run id (initial id size tracked) (events.take count)).state :=
  preserves id _ (initial_formed id size tracked) _ (schedule_take id _ events scheduled count)

/-- After real endCall bookkeeping, raw frame coverage restores current root
Write ownership from the policy derived by history induction. Implicit tree
protector-end accesses are not represented by this separate bookkeeping step. -/
theorem after_end_call_from_seed (id : AllocId) (size : Size) (tracked : Array BorTag) (events : List Event)
    (scheduled : Schedule id (initial id size tracked) events) (count : Nat) (frame : FrameState)
    (covered : let state:=(GeneralBorrowForestGeneratedTagHistory.run id (initial id size tracked) (events.take count)).state
      ∀row∈state.tree.nodes.entries,state.global.protectedTags.contains row.2.tag=false ∨∃allocation,(allocation,row.2.tag)∈frame.protectedTags.toList)
    (lower upper : UInt64) :
    let state:=(GeneralBorrowForestGeneratedTagHistory.run id (initial id size tracked) (events.take count)).state
    OwnedOn (GeneralBorrowRange.LocationOwned state.tree (state.global.endCall frame).protectedTags ⟨0⟩ .Write) lower upper state.tree.locations :=
  GeneralBorrowStructuralHistoryRootAuthorityState.after_end_call _ ⟨0⟩ (from_seed id size tracked events scheduled count).authority _ frame covered lower upper
end DuplicatePrefix.GeneralBorrowForestGeneratedRootAuthority
