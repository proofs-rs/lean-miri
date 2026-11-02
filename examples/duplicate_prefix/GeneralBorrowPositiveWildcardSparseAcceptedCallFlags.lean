import duplicate_prefix.GeneralBorrowPositiveWildcardSparseAcceptedCallSource
import duplicate_prefix.GeneralBorrowPositiveWildcardSparseAcceptedSlotFlags
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardSparseAcceptedCallFlags
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
/-- The actual helper's ended protector table is the source-issued table. -/
theorem table (s : GeneralBorrowPositiveWildcardSparseAcceptedInput.Initial) (updated : Allocation Provenance BorrowTree)
    (call : GeneralBorrowExposedScopedWritableAsMutToCopy.Input)
    (source : GeneralBorrowPositiveWildcardSparseAcceptedCallSource.Facts s updated call) :
    ((GeneralBorrowExposedScopedWritableAsMutCallInput.held call.toInput).global.endCall
      (({} : FrameState).addProtector call.id call.tracker.global.nextPointerTag)).protectedTags=
      (GeneralBorrowPositiveWildcardSparseAcceptedUnheld.mutableEnded s).protectedTags := by
  simp only [GeneralBorrowExposedScopedWritableAsMutCallInput.held,TypedBorrowSteps.registeredTracker,
    TypedBorrowSteps.registeredGlobal,ReferenceBorrowDriver.allocatedTracker,GlobalState.endCall]
  rw [source.tracker,source.id]
  rfl
end DuplicatePrefix.GeneralBorrowPositiveWildcardSparseAcceptedCallFlags
