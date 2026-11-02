import duplicate_prefix.GeneralBorrowPositiveWildcardSparseAccepted
import duplicate_prefix.GeneralBorrowPositiveWildcardSparseAcceptedFinish
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardSparseAcceptedSafety
open Miri
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
/-- The accepted positive original wildcard call returns through the fixed
physical interpreter. All permitted finite prefixes have a successful step. -/
theorem invoke (s : GeneralBorrowPositiveWildcardSparseAcceptedCompleteInput.Initial) :
    GeneralBorrowPositiveWildcardSparseAllCountResult.Result s.toAccepted.toInitial.toBase := by
  obtain ⟨input,installed,options,limits,remaining,span,call,prefixTrace⟩ :=
    GeneralBorrowPositiveWildcardSparseAccepted.prepare s
  exact GeneralBorrowPositiveWildcardSparseAcceptedFinish.finish s installed input options limits remaining span call prefixTrace
end DuplicatePrefix.GeneralBorrowPositiveWildcardSparseAcceptedSafety
