import duplicate_prefix.GeneralBorrowPositiveConcreteWindowAccepted
import duplicate_prefix.GeneralBorrowPositiveConcreteWindowAcceptedFinish
namespace DuplicatePrefix.GeneralBorrowPositiveConcreteWindowAcceptedSafety
open Miri
variable [area : GeneralBorrowExposedKnownRootState.Scope]
variable {profileMode : ProfileMode}
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
/-- The accepted positive original wildcard call returns through the fixed
physical interpreter. All permitted finite prefixes have a successful step. -/
theorem invoke (s : GeneralBorrowPositiveConcreteWindowAcceptedCompleteInput.InitialFor profileMode) :
    GeneralBorrowPositiveConcreteWindowAllCountResult.Result s.toAccepted.toInitial.toBase := by
  obtain ⟨input,installed,options,limits,remaining,span,call,prefixTrace⟩ :=
    GeneralBorrowPositiveConcreteWindowAccepted.prepare s
  exact GeneralBorrowPositiveConcreteWindowAcceptedFinish.finish s installed input options limits remaining span call prefixTrace
end DuplicatePrefix.GeneralBorrowPositiveConcreteWindowAcceptedSafety
