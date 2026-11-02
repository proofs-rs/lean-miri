import duplicate_prefix.GeneralBorrowPositiveWildcardAccepted
import duplicate_prefix.GeneralBorrowPositiveWildcardAcceptedFinish
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardAcceptedSafety
open Miri
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
/-- The accepted positive original wildcard call returns through the fixed
physical interpreter. All permitted finite prefixes have a successful step. -/
theorem invoke (s : GeneralBorrowPositiveWildcardAcceptedCompleteInput.Initial) :
    GeneralBorrowPositiveWildcardAllCountResult.Result s.toAccepted.toInitial.toBase := by
  obtain ⟨input,installed,options,limits,remaining,span,call,prefixTrace⟩ :=
    GeneralBorrowPositiveWildcardAccepted.prepare s
  exact GeneralBorrowPositiveWildcardAcceptedFinish.finish s installed input options limits remaining span call prefixTrace
end DuplicatePrefix.GeneralBorrowPositiveWildcardAcceptedSafety
