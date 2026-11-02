import duplicate_prefix.GeneralBorrowPositiveWildcardPartitionAcceptedInput
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardPartitionAcceptedCompleteInput
open Miri
variable [area : GeneralBorrowExposedKnownRootState.Scope]
/-- Both physical statement validation and reflected configuration use the
same initial validation budget. -/
structure Initial extends toAccepted : GeneralBorrowPositiveWildcardPartitionAcceptedInput.Initial where
  statementFuel : limits.validation=validityFuel+1
end DuplicatePrefix.GeneralBorrowPositiveWildcardPartitionAcceptedCompleteInput
