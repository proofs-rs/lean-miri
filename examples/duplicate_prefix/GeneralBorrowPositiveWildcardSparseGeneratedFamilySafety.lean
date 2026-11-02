import duplicate_prefix.GeneralBorrowPositiveWildcardSparseFamilyInput
import duplicate_prefix.GeneralBorrowPositiveWildcardSparseAllCountSafety
import duplicate_prefix.GeneralBorrowSparseExposedRootAccessGenerated
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardSparseGeneratedFamilySafety
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open GeneralBorrowPositiveWildcardFamilyPhysical GeneralBorrowSparseExposedRootFormation
open GeneralBorrowSparseExposedRootAccessGenerated
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section
/-- Actual root allocation, exposure, partial-root formation and bounded
Read/Write history supply the mixed/sparse borrow premises of the original
all-count physical invocation. Physical caller data and numeric room remain
explicit. This connects a SourceModel history, not arbitrary Rust histories. -/
theorem invoke (capacity : UInt64) (nonzero : capacity≠0)
    (windows : List (Window capacity)) (room : windows.length+9<65536)
    (events : List (GeneralBorrowSparseExposedLeafHistory.Event capacity))
    (p : Caller capacity (source capacity nonzero windows room events).global
      (source capacity nonzero windows room events).tree)
    (sameAllocation : p.id=GeneralBorrowProtectedLifetimeSeed.allocation) :
    let state:=source capacity nonzero windows room events
    GlobalState.new.rootPointerTag p.id=.ok (GeneralBorrowProtectedLifetimeSeed.global,BorTag.one) ∧
    Nonempty (Generated capacity nonzero windows room events) ∧
    @GeneralBorrowPositiveWildcardSparseAllCountResult.Result (scope (state.primary::state.extras))
      (GeneralBorrowPositiveWildcardSparseFamilyInput.base state p nonzero
        (emptyProtections capacity nonzero windows room events)) := by
  let state:=source capacity nonzero windows room events
  let generated:=build capacity nonzero windows room events
  refine ⟨?_,⟨generated⟩,?_⟩
  · rw [sameAllocation]
    exact generated.allocated
  · letI : GeneralBorrowExposedKnownRootState.Scope:=scope (state.primary::state.extras)
    exact GeneralBorrowPositiveWildcardSparseAllCountSafety.invoke
      (GeneralBorrowPositiveWildcardSparseFamilyInput.initial state p nonzero
        (emptyProtections capacity nonzero windows room events))
end
end DuplicatePrefix.GeneralBorrowPositiveWildcardSparseGeneratedFamilySafety
