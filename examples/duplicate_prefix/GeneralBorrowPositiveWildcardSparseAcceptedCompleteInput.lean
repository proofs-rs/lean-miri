import duplicate_prefix.GeneralBorrowPositiveWildcardSparseAcceptedInput
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardSparseAcceptedCompleteInput
open Miri
variable [area : GeneralBorrowExposedKnownRootState.Scope]
/-- Both physical statement validation and reflected configuration use the
same initial validation budget. -/
structure Initial extends toAccepted : GeneralBorrowPositiveWildcardSparseAcceptedInput.Initial where
  statementFuel : limits.validation=validityFuel+1
end DuplicatePrefix.GeneralBorrowPositiveWildcardSparseAcceptedCompleteInput
