import duplicate_prefix.PositiveRootInvocationState
import duplicate_prefix.PositiveLenPost
namespace DuplicatePrefix.PositiveRootTagGrowth
open Miri Miri.Memory Miri.TreeBorrows Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Checked freshness makes tag allocation a genuine natural-number successor. -/
theorem successor_value (tag : BorTag) (fresh : tag.value < 18446744073709551615) :
    (TypedRetagEmpty.successorTag tag fresh).value.toNat = tag.value.toNat+1 := by
  have bounded : tag.value.toNat < 18446744073709551615 := by
    simpa [UInt64.lt_iff_toNat_lt] using fresh
  have fits : tag.value.toNat+1 < 2^64 := by omega
  simp only [TypedRetagEmpty.successorTag,UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt fits]

theorem successor_strict (tag : BorTag) (fresh : tag.value < 18446744073709551615) :
    tag.value.toNat < (TypedRetagEmpty.successorTag tag fresh).value.toNat := by
  rw [successor_value]
  omega

/-- In the actual positive invocation's allocation sequence, the return-slot
child precedes the final helper tag. Every premise is a counter freshness bound;
protection registration and call release do not change the counter. -/
theorem slot_child_not_last (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (slotFresh : (PositiveRootInvocationState.next tracker fresh).global.nextPointerTag.value < 18446744073709551615)
    (thirdFresh : (PositiveRootInvocationState.held tracker fresh slotFresh).global.nextPointerTag.value < 18446744073709551615)
    (fourthFresh : (ReferenceBorrowDriver.allocatedTracker (PositiveRootInvocationState.held tracker fresh slotFresh) thirdFresh).global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId)
    (fifthFresh : (PositiveLenPost.trackerAfter (ReferenceBorrowDriver.allocatedTracker (PositiveRootInvocationState.held tracker fresh slotFresh) thirdFresh) fourthFresh id).global.nextPointerTag.value < 18446744073709551615) :
    (PositiveRootInvocationState.next tracker fresh).global.nextPointerTag ≠
      TypedRetagEmpty.successorTag (PositiveLenPost.trackerAfter
        (ReferenceBorrowDriver.allocatedTracker (PositiveRootInvocationState.held tracker fresh slotFresh) thirdFresh)
        fourthFresh id).global.nextPointerTag fifthFresh := by
  have step2 := successor_value (PositiveRootInvocationState.next tracker fresh).global.nextPointerTag slotFresh
  have step3 := successor_value (PositiveRootInvocationState.held tracker fresh slotFresh).global.nextPointerTag thirdFresh
  have step4 := successor_value (ReferenceBorrowDriver.allocatedTracker (PositiveRootInvocationState.held tracker fresh slotFresh) thirdFresh).global.nextPointerTag fourthFresh
  have step5 := successor_value (PositiveLenPost.trackerAfter (ReferenceBorrowDriver.allocatedTracker (PositiveRootInvocationState.held tracker fresh slotFresh) thirdFresh) fourthFresh id).global.nextPointerTag fifthFresh
  change (PositiveRootInvocationState.held tracker fresh slotFresh).global.nextPointerTag.value.toNat =
    (PositiveRootInvocationState.next tracker fresh).global.nextPointerTag.value.toNat+1 at step2
  change (ReferenceBorrowDriver.allocatedTracker (PositiveRootInvocationState.held tracker fresh slotFresh) thirdFresh).global.nextPointerTag.value.toNat =
    (PositiveRootInvocationState.held tracker fresh slotFresh).global.nextPointerTag.value.toNat+1 at step3
  change (PositiveLenPost.trackerAfter (ReferenceBorrowDriver.allocatedTracker (PositiveRootInvocationState.held tracker fresh slotFresh) thirdFresh) fourthFresh id).global.nextPointerTag.value.toNat =
    (ReferenceBorrowDriver.allocatedTracker (PositiveRootInvocationState.held tracker fresh slotFresh) thirdFresh).global.nextPointerTag.value.toNat+1 at step4
  intro same
  have equal := congrArg (fun tag : BorTag => tag.value.toNat) same
  omega
end DuplicatePrefix.PositiveRootTagGrowth
