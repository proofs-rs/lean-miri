import duplicate_prefix.GeneralBorrowPositiveWildcardWindowAcceptedInput
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardWindowAcceptedCompleteInput
open Miri Miri.ABI
variable [area : GeneralBorrowExposedKnownRootState.Scope]
/-- Both physical statement validation and reflected configuration use the
same initial validation budget. -/
structure Initial extends toAccepted : GeneralBorrowPositiveWildcardWindowAcceptedInput.Initial where
  sourceInitialized : InitMaskCopy.InitializedOn entry.allocation.initializationMask (Size.ofBytes offset) (Size.ofBytes (offset+count))
  statementFuel : limits.validation=validityFuel+1
end DuplicatePrefix.GeneralBorrowPositiveWildcardWindowAcceptedCompleteInput
