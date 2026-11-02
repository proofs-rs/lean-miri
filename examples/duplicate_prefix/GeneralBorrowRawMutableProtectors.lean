import duplicate_prefix.GeneralBorrowRawDefaultResources
namespace DuplicatePrefix.GeneralBorrowRawMutableProtectors
open Miri Miri.Memory Miri.ABI Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
private theorem insert_remove (tags : ProtectedTags) (tag : BorTag) (kind : ProtectorKind)
    (different : ∀ row ∈ tags.entries, row.1 ≠ tag) : (tags.insert tag kind).remove tag = tags := by
  have unchanged : tags.entries.filter (fun row => row.1 != tag) = tags.entries := by
    apply Array.filter_eq_self.mpr
    intro row member
    simpa only [bne_iff_ne] using different row member
  unfold ProtectedTags.insert ProtectedTags.remove
  simp only [Array.filter_push,bne_self_eq_false,Bool.false_eq_true,↓reduceIte,unchanged]

/-- The temporary helper's real addProtector/endCall leaves the complete
original protector table unchanged; freshness follows from raw high-water. -/
theorem unchanged (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawDefault.Input tree tracker.global)
    (headroom : tree.nodes.size+2 < 65536)
    (tagsRoom : tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615)
    (fresh : (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom).global.nextPointerTag.value < 18446744073709551615) :
    let allocated := ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom
    let held := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker allocated fresh) allocated.global.nextPointerTag
    (held.global.endCall (({} : FrameState).addProtector allocation allocated.global.nextPointerTag)).protectedTags = tracker.global.protectedTags := by
  let allocated := ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom
  have data := GeneralBorrowRawDefaultResources.resources tree tracker runtime input headroom tagsRoom
  dsimp only at data
  obtain ⟨defaultRuntime,_,_,next,_,_,_,_,_⟩ := data
  change (tracker.global.protectedTags.insert allocated.global.nextPointerTag .StrongProtector).remove allocated.global.nextPointerTag = tracker.global.protectedTags
  apply insert_remove
  intro row member same
  have below := defaultRuntime.below.protectors row member
  rw [same] at below
  exact Nat.lt_irrefl _ below
end DuplicatePrefix.GeneralBorrowRawMutableProtectors
