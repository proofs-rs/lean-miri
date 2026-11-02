import duplicate_prefix.GeneralBorrowPositiveWildcardPartitionAccepted
import duplicate_prefix.GeneralBorrowPositiveWildcardPartitionAcceptedFinish
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardPartitionAcceptedSafety
open Miri
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
/-- The accepted positive original wildcard call returns through the fixed
physical interpreter. All permitted finite prefixes have a successful step. -/
theorem invoke (s : GeneralBorrowPositiveWildcardPartitionAcceptedCompleteInput.Initial) :
    GeneralBorrowPositiveWildcardPartitionAllCountResult.Result s.toAccepted.toInitial.toBase := by
  obtain ⟨input,installed,options,limits,remaining,span,call,prefixTrace⟩ :=
    GeneralBorrowPositiveWildcardPartitionAccepted.prepare s
  exact GeneralBorrowPositiveWildcardPartitionAcceptedFinish.finish s installed input options limits remaining span call prefixTrace
end DuplicatePrefix.GeneralBorrowPositiveWildcardPartitionAcceptedSafety
