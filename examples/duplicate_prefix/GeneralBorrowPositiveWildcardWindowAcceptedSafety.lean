import duplicate_prefix.GeneralBorrowPositiveWildcardWindowAccepted
import duplicate_prefix.GeneralBorrowPositiveWildcardWindowAcceptedFinish
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardWindowAcceptedSafety
open Miri
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
/-- The accepted positive original wildcard call returns through the fixed
physical interpreter. All permitted finite prefixes have a successful step. -/
theorem invoke (s : GeneralBorrowPositiveWildcardWindowAcceptedCompleteInput.Initial) :
    GeneralBorrowPositiveWildcardWindowAllCountResult.Result s.toAccepted.toInitial.toBase := by
  obtain ⟨input,installed,options,limits,remaining,span,call,prefixTrace⟩ :=
    GeneralBorrowPositiveWildcardWindowAccepted.prepare s
  exact GeneralBorrowPositiveWildcardWindowAcceptedFinish.finish s installed input options limits remaining span call prefixTrace
end DuplicatePrefix.GeneralBorrowPositiveWildcardWindowAcceptedSafety
