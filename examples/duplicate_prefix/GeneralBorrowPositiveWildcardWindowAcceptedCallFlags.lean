import duplicate_prefix.GeneralBorrowPositiveWildcardWindowAcceptedCallSource
import duplicate_prefix.GeneralBorrowPositiveWildcardWindowAcceptedSlotFlags
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardWindowAcceptedCallFlags
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
/-- The actual helper's ended protector table is the source-issued table. -/
theorem table (s : GeneralBorrowPositiveWildcardWindowAcceptedInput.Initial) (updated : Allocation Provenance BorrowTree)
    (call : GeneralBorrowExposedScopedWindowWritableAsMutToCopy.Input)
    (source : GeneralBorrowPositiveWildcardWindowAcceptedCallSource.Facts s updated call) :
    ((GeneralBorrowExposedScopedWindowWritableAsMutCallInput.held call.toInput).global.endCall
      (({} : FrameState).addProtector call.id call.tracker.global.nextPointerTag)).protectedTags=
      (GeneralBorrowPositiveWildcardWindowAcceptedUnheld.mutableEnded s).protectedTags := by
  simp only [GeneralBorrowExposedScopedWindowWritableAsMutCallInput.held,TypedBorrowSteps.registeredTracker,
    TypedBorrowSteps.registeredGlobal,ReferenceBorrowDriver.allocatedTracker,GlobalState.endCall]
  rw [source.tracker,source.id]
  rfl
end DuplicatePrefix.GeneralBorrowPositiveWildcardWindowAcceptedCallFlags
