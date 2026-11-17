import duplicate_prefix.PositiveLenPost
import duplicate_prefix.GeneralBorrowFnEntryRegistrationRuntime
namespace DuplicatePrefix.CurrentCallEmptyLiveHelperGlobal
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
private theorem insert_remove (tags : ProtectedTags) (tag : BorTag) (kind : ProtectorKind)
    (different : ∀row∈tags.entries,row.1≠tag) : (tags.insert tag kind).remove tag=tags := by
  have unchanged : tags.entries.filter (fun row=>row.1!=tag)=tags.entries := by
    apply Array.filter_eq_self.mpr
    intro row member
    simpa only [bne_iff_ne] using different row member
  unfold ProtectedTags.insert ProtectedTags.remove
  simp only [Array.filter_push,bne_self_eq_false,Bool.false_eq_true,↓reduceIte,unchanged]

/-- The actual zero Shared tag and temporary Len protector consume two tags.
The real Len endCall restores the complete original protector table. -/
theorem facts (tree : BorrowTree) (tracker : MachineHooks.BorrowState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (first : tracker.global.nextPointerTag.value<18446744073709551615)
    (second : (ReferenceBorrowDriver.allocatedTracker tracker first).global.nextPointerTag.value<18446744073709551615)
    (id : AllocId) :
    let final:=PositiveLenPost.trackerAfter (ReferenceBorrowDriver.allocatedTracker tracker first) second id
    final.global={tracker.global with nextPointerTag:=final.global.nextPointerTag} ∧
    final.global.nextPointerTag.value.toNat=tracker.global.nextPointerTag.value.toNat+2 ∧
    final.retagMode=tracker.retagMode := by
  let expr:=ReferenceBorrowDriver.allocatedTracker tracker first
  let final:=PositiveLenPost.trackerAfter expr second id
  have freshFlags : ∀row∈tracker.global.protectedTags.entries,row.1≠expr.global.nextPointerTag := by
    intro row member same
    have bound:=runtime.below.protectors row member
    have successor:=GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag first
    change expr.global.nextPointerTag.value.toNat=tracker.global.nextPointerTag.value.toNat+1 at successor
    rw [same,successor] at bound
    omega
  have roundTrip:=insert_remove tracker.global.protectedTags expr.global.nextPointerTag .StrongProtector freshFlags
  refine ⟨?_,?_,rfl⟩
  · change ({tracker.global with
      nextPointerTag := (ReferenceBorrowDriver.allocatedTracker expr second).global.nextPointerTag
      protectedTags := (tracker.global.protectedTags.insert expr.global.nextPointerTag .StrongProtector).remove expr.global.nextPointerTag} : GlobalState)=
      {tracker.global with nextPointerTag:=(ReferenceBorrowDriver.allocatedTracker expr second).global.nextPointerTag}
    rw [roundTrip]
  · change (TypedRetagEmpty.successorTag expr.global.nextPointerTag second).value.toNat=_
    rw [GenericFunctionEntryNumerics.successor_value]
    change (TypedRetagEmpty.successorTag tracker.global.nextPointerTag first).value.toNat+1=_
    rw [GenericFunctionEntryNumerics.successor_value]
end DuplicatePrefix.CurrentCallEmptyLiveHelperGlobal
