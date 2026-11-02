import duplicate_prefix.GeneralBorrowPositiveConcreteWindowAcceptedCallSource
import duplicate_prefix.GeneralBorrowPositiveConcreteWindowAcceptedSlotFlags
namespace DuplicatePrefix.GeneralBorrowPositiveConcreteWindowAcceptedCallFlags
variable {profileMode : ProfileMode}
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
/-- The actual helper's ended protector table is the source-issued table. -/
theorem table (s : GeneralBorrowPositiveConcreteWindowAcceptedInput.InitialFor profileMode) (updated : Allocation Provenance BorrowTree)
    (call : GeneralBorrowExposedScopedInactiveWritableAsMutToCopy.InputFor profileMode)
    (source : GeneralBorrowPositiveConcreteWindowAcceptedCallSource.Facts s updated call) :
    ((GeneralBorrowExposedScopedInactiveWritableAsMutCallInput.held call.toInput).global.endCall
      (({} : FrameState).addProtector call.id call.tracker.global.nextPointerTag)).protectedTags=
      (GeneralBorrowPositiveConcreteWindowAcceptedUnheld.mutableEnded s).protectedTags := by
  simp only [GeneralBorrowExposedScopedInactiveWritableAsMutCallInput.held,TypedBorrowSteps.registeredTracker,
    TypedBorrowSteps.registeredGlobal,ReferenceBorrowDriver.allocatedTracker,GlobalState.endCall]
  rw [source.tracker,source.id]
  rfl
end DuplicatePrefix.GeneralBorrowPositiveConcreteWindowAcceptedCallFlags
