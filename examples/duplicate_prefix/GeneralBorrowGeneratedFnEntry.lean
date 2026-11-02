import duplicate_prefix.GeneralBorrowGeneratedFnEntryRead
import duplicate_prefix.GeneralBorrowRootAuthorityReadFormed
namespace DuplicatePrefix.GeneralBorrowGeneratedFnEntry
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestGeneratedTagHistoryData GeneralBorrowGeneratedFnEntryRead
set_option maxRecDepth 65536
set_option maxHeartbeats 2500000

structure Output where
  state : Snapshot
  access : BorrowTree.BorrowTreeAccessResult
  child : BorrowTree.ChildInsertResult

/-- Actual counter allocation and optional Strong registration precede the
bounded concrete parent Read and newChild. All failure records are retained. -/
def operation (id : AllocId) (state : Snapshot) (parent : BorTag) (offset len : Size)
    (inside : DedupRangeMap LocationState) (outside : Permission) (held : Bool) (mode : ChildrenVisitMode) : Except GlobalStateError Output := do
  let (advanced,tag) ← state.global.newPointerTag
  let registered := register id state advanced tag held
  let access := state.tree.performNormalAccessRange parent offset len .Read registered.global.protectedTags mode
  let child := access.tree.newChild offset (.concrete parent) tag inside outside held
  pure ⟨{registered with tree:=child.tree},access,child⟩

structure Formed (id : AllocId) (root : UniIndex) (state : Snapshot) : Prop where
  frames : GeneralBorrowProtectedGeneratedFramesStep.Formed id root state
  readable : GeneralBorrowForestGeneratedReadableHistory.Formed state
  authority : GeneralBorrowStructuralHistoryRootAuthorityState.Formed state.tree ⟨0⟩
  covered : GeneralBorrowForestGeneratedRootEndFrames.Covered state

/-- Initial raw source constructor policy plus a bounded positive leading Read.
No success, intermediate readable/Frames or final owner is requested. -/
def Applicable (state : Snapshot) (parent : BorTag) (offset len : Size)
    (inside : DedupRangeMap LocationState) (outside : Permission) (held : Bool) : Prop :=
  GeneralBorrowForestGeneratedReadableHistory.Applicable state (.constructor (.concrete parent) offset inside outside held) ∧
  offset.bytes.toNat+len.bytes.toNat≤state.tree.locations.size.bytes.toNat ∧ len.bytes≠0

theorem invoke (id : AllocId) (state : Snapshot) (formed : Formed id ⟨0⟩ state)
    (parent : BorTag) (offset len : Size) (inside : DedupRangeMap LocationState) (outside : Permission)
    (held : Bool) (mode : ChildrenVisitMode) (allowed : Applicable state parent offset len inside outside held) :
    ∃ output,operation id state parent offset len inside outside held mode=.ok output ∧
      output.access.status=.Completed ∧ output.child.outcome=.ok () ∧ Formed id ⟨0⟩ output.state := by
  have room := allowed.1.1.1.1
  obtain ⟨anchor,node,tagged,present⟩ := allowed.1.1.1.2.2.1
  let before := shadow id state room held parent offset len mode
  let registered := registration id state room held
  let access := read id state room held parent offset len mode
  let child := access.tree.newChild offset (.concrete parent) state.global.nextPointerTag inside outside held
  have prepared := prepare id ⟨0⟩ state formed.frames formed.readable room held parent anchor node tagged present offset len mode allowed.2.1
  have frame : before.tree = {state.tree with locations:=access.tree.locations} := prepared.2.2.2.2
  have sizeEq : before.tree.locations.size=state.tree.locations.size := prepared.2.2.2.1
  have sourceAllowed : GeneralBorrowForestGeneratedReadableHistory.Applicable before (.constructor (.concrete parent) offset inside outside held) := by
    obtain ⟨⟨counterRoom,nodeRoom,parentData,initialOutside,notUnique,foreign,bounded,insideInitial⟩,sifaInside⟩ := allowed.1.1
    refine ⟨⟨⟨counterRoom,?_,?_,initialOutside,notUnique,foreign,?_,insideInitial⟩,sifaInside⟩,allowed.1.2⟩
    · change before.tree.nodes.size+1≤4294967295
      rw [frame]
      exact nodeRoom
    · exact ⟨anchor,node,by rw [frame];exact tagged,by rw [frame];exact present⟩
    · rw [sizeEq]
      exact bounded
  have nextFrames := GeneralBorrowProtectedGeneratedFramesStep.preserves id ⟨0⟩ before prepared.2.1 _ sourceAllowed
  have nextReadable := GeneralBorrowForestGeneratedReadableHistory.step_formed id before prepared.2.2.1 _ sourceAllowed
  have registeredReadable : GeneralRangeMapState.Every (fun location=>GeneralBorrowPhysicalReadable.Profile state.tree location registered.global.protectedTags) state.tree.locations := by
    have fresh := GeneralBorrowForestGeneratedTagHistoryData.fresh state formed.frames.cache.sifa.generated
    cases held with
    | false => exact formed.readable.readable
    | true =>
      exact GeneralBorrowPhysicalReadableProtections.register state.tree
        {state.global with nextPointerTag:=TypedRetagEmpty.successorTag state.global.nextPointerTag room}
        {} id state.global.nextPointerTag .StrongProtector fresh formed.frames.cache.sifa.generated.structural.allocator.nodeTags formed.readable.readable
  have nextAuthority := GeneralBorrowRootAuthorityReadFormed.ranged state.tree registered.global.protectedTags parent anchor ⟨0⟩ offset len mode
    formed.authority formed.frames.roots node present tagged registeredReadable allowed.2.1
  have shadowAuthority : GeneralBorrowForestGeneratedRootAuthority.Formed before := ⟨prepared.2.1.cache.sifa,nextAuthority.2.1⟩
  have authority := GeneralBorrowForestGeneratedRootAuthority.step_formed id before shadowAuthority _
    (GeneralBorrowForestGeneratedReadablePrepared.authority_guard before _ sourceAllowed)
  have nextCovered := GeneralBorrowForestGeneratedRootEndFrames.step_cover id before formed.covered _
    (GeneralBorrowForestGeneratedReadablePrepared.authority_guard before _ sourceAllowed)
  have flags := GeneralBorrowForestGeneratedTagHistoryFlags.generated id before prepared.2.1.cache.sifa.generated room held
  let output : Output := ⟨{registered with tree:=child.tree},access,child⟩
  have finalEq : (step id before (.constructor (.concrete parent) offset inside outside held)).state=output.state := by
    simp only [step,flags.1]
    cases held <;> rfl
  have childOk : child.outcome=.ok () := by
    have completed := nextFrames.1
    simp only [step,flags.1] at completed
    exact of_decide_eq_true completed
  refine ⟨output,?_,prepared.1,childOk,?_⟩
  · simp only [operation,TypedRetagEmpty.allocate_tag state.global room,Except.bind,Except.pure,bind,pure]
    rfl
  · rw [←finalEq]
    exact ⟨nextFrames.2,nextReadable,authority.authority,nextCovered⟩
end DuplicatePrefix.GeneralBorrowGeneratedFnEntry
