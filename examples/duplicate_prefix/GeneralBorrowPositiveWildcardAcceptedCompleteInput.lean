import duplicate_prefix.GeneralBorrowPositiveWildcardAcceptedInput
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardAcceptedCompleteInput
open Miri
variable [area : GeneralBorrowExposedKnownRootState.Scope]
/-- Both physical statement validation and reflected configuration use the
same initial validation budget. -/
structure Initial extends toAccepted : GeneralBorrowPositiveWildcardAcceptedInput.Initial where
  statementFuel : limits.validation=validityFuel+1
end DuplicatePrefix.GeneralBorrowPositiveWildcardAcceptedCompleteInput
