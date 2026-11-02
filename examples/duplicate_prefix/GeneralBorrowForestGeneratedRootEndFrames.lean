import duplicate_prefix.GeneralBorrowForestGeneratedRootAuthority
namespace DuplicatePrefix.GeneralBorrowForestGeneratedRootEndFrames
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestGeneratedTagHistoryData GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Every actual held global tag has its source-owned provenance record in an
actual stored generated frame. This is derived from registrations, not supplied
as a final protector-coverage certificate. -/
def Covered (state : Snapshot) : Prop :=
  ∀tag,state.global.protectedTags.contains tag=true→∃row∈state.frames,∃allocation,(allocation,tag)∈row.2.protectedTags.toList

private theorem register_cover (id : AllocId) (state : Snapshot) (allocated : GlobalState)
    (same : allocated.protectedTags=state.global.protectedTags) (tag : BorTag) (held : Bool) (initial : Covered state) :
    Covered (register id state allocated tag held) := by
  cases held with
  | false => simpa only [register,Bool.false_eq_true,↓reduceIte,Covered,same] using initial
  | true =>
    intro query current
    change (allocated.protectedTags.insert tag .StrongProtector).contains query=true at current
    change ∃row∈state.frames.push (tag,({}:FrameState).addProtector id tag),∃allocation,(allocation,query)∈row.2.protectedTags.toList
    by_cases different : query≠tag
    · rw[ProtectorInsertion.contains_other allocated.protectedTags tag query .StrongProtector different,same] at current
      obtain ⟨row,member,allocation,stored⟩:=initial query current
      exact ⟨row,Array.mem_push.mpr (Or.inl member),allocation,stored⟩
    · have equal : query=tag := Classical.byContradiction different
      subst query
      refine ⟨(tag,({}:FrameState).addProtector id tag),by simp,id,?_⟩
      simp [FrameState.addProtector]

theorem step_cover (id : AllocId) (state : Snapshot) (initial : Covered state) (event : Event)
    (allowed : GeneralBorrowForestGeneratedRootAuthority.Applicable state event) : Covered (step id state event).state := by
  cases event with
  | access source offset len kind mode => exact False.elim allowed.1.2
  | release => exact False.elim allowed.1.2
  | allocate =>
    have actual:=TypedRetagEmpty.allocate_tag state.global allowed.1.1
    simpa only [step,actual,Covered] using initial
  | gc live => exact initial
  | constructor parent base inside outside held =>
    have room:=allowed.1.1.1
    let allocated : GlobalState := {state.global with nextPointerTag:=TypedRetagEmpty.successorTag state.global.nextPointerTag room}
    have actual : state.global.newPointerTag=.ok (allocated,state.global.nextPointerTag):=TypedRetagEmpty.allocate_tag state.global room
    simpa only [step,actual,Covered] using register_cover id state allocated rfl state.global.nextPointerTag held initial

theorem covered (id : AllocId) (state : Snapshot) (initial : Covered state) (events : List Event)
    (scheduled : GeneralBorrowForestGeneratedRootAuthority.Schedule id state events) :
    Covered (GeneralBorrowForestGeneratedTagHistory.run id state events).state := by
  induction events generalizing state with
  | nil => exact initial
  | cons event rest ih =>
    have next:=step_cover id state initial event scheduled.1
    cases completed : (step id state event).completed with
    | false => simpa only [GeneralBorrowForestGeneratedTagHistory.run,completed,Bool.false_eq_true,↓reduceIte] using next
    | true => simpa only [GeneralBorrowForestGeneratedTagHistory.run,completed,↓reduceIte] using ih _ next (scheduled.2 completed)

theorem initial_cover (id : AllocId) (size : Size) (tracked : Array BorTag) : Covered (initial id size tracked) := by
  intro tag held
  change ({}:ProtectedTags).contains tag=true at held
  simp [ProtectedTags.contains,ProtectedTags.get] at held

/-- Exact source endCall bookkeeping for a supplied pop-order frame sequence.
This does not execute or certify the preceding implicit tree-release accesses. -/
def endFrames (global : GlobalState) (frames : List (BorTag×FrameState)) : GlobalState :=
  frames.foldl (fun current row=>current.endCall row.2) global

private theorem absent (global : GlobalState) (frames : List (BorTag×FrameState)) (tag : BorTag)
    (unheld : global.protectedTags.contains tag=false) : (endFrames global frames).protectedTags.contains tag=false := by
  induction frames generalizing global with
  | nil => exact unheld
  | cons frame rest ih =>
    apply ih
    cases held : (global.endCall frame.2).protectedTags.contains tag with
    | false => rfl
    | true =>
      have original:=GeneralBorrowRelease.end_call_weakens global frame.2 tag held
      rw[unheld] at original
      cases original

private theorem owned_absent (global : GlobalState) (frames : List (BorTag×FrameState)) (tag : BorTag)
    (owned : ∃row∈frames,∃allocation,(allocation,tag)∈row.2.protectedTags.toList) :
    (endFrames global frames).protectedTags.contains tag=false := by
  induction frames generalizing global with
  | nil => simp at owned
  | cons first rest ih =>
    obtain ⟨row,member,allocation,stored⟩:=owned
    rcases List.mem_cons.mp member with same | later
    · subst row
      exact absent (global.endCall first.2) rest tag (GeneralBorrowRelease.end_call_owned_absent global first.2 allocation tag stored)
    · exact ih (global.endCall first.2) ⟨row,later,allocation,stored⟩

theorem closed_unheld (state : Snapshot) (cover : Covered state) (tag : BorTag) :
    (endFrames state.global state.frames.toList.reverse).protectedTags.contains tag=false := by
  cases held : state.global.protectedTags.contains tag with
  | false => exact absent state.global state.frames.toList.reverse tag held
  | true =>
    obtain ⟨row,member,allocation,stored⟩:=cover tag held
    have membership : row∈state.frames.toList.reverse := by
      simpa only [List.mem_reverse] using (Array.mem_toList_iff.mpr member : row∈state.frames.toList)
    exact owned_absent state.global state.frames.toList.reverse tag ⟨row,membership,allocation,stored⟩

/-- Complete generated constructor/GC chronology derives latent authority and
frame provenance coverage internally. Actual endCall folds then restore real
root Write ownership, with no final owner/unheld/frame-coverage premise. This
is the bookkeeping endpoint, not a claim about arbitrary Rust stack popping. -/
theorem from_seed (id : AllocId) (size : Size) (tracked : Array BorTag) (events : List Event)
    (scheduled : GeneralBorrowForestGeneratedRootAuthority.Schedule id (initial id size tracked) events) (count : Nat) (lower upper : UInt64) :
    let state:=(GeneralBorrowForestGeneratedTagHistory.run id (initial id size tracked) (events.take count)).state
    OwnedOn (GeneralBorrowRange.LocationOwned state.tree (endFrames state.global state.frames.toList.reverse).protectedTags ⟨0⟩ .Write) lower upper state.tree.locations := by
  let state:=(GeneralBorrowForestGeneratedTagHistory.run id (initial id size tracked) (events.take count)).state
  have authority:=GeneralBorrowForestGeneratedRootAuthority.from_seed id size tracked events scheduled count
  have coverage:=covered id _ (initial_cover id size tracked) _ (GeneralBorrowForestGeneratedRootAuthority.schedule_take id _ events scheduled count)
  apply GeneralBorrowStructuralHistoryRootAuthorityState.owned state.tree ⟨0⟩ authority.authority _ _ lower upper
  intro row member
  exact closed_unheld state coverage row.2.tag
end DuplicatePrefix.GeneralBorrowForestGeneratedRootEndFrames
