import duplicate_prefix.GeneralBorrowPositiveConcreteWindowAcceptedInput
namespace DuplicatePrefix.GeneralBorrowPositiveConcreteWindowAcceptedCompleteInput
variable [area : GeneralBorrowExposedKnownRootState.Scope]
/-- Explicit call-time statement-validation budget for the accepted branch. -/
structure InitialFor (profileMode : ProfileMode) extends toAccepted : GeneralBorrowPositiveConcreteWindowAcceptedInput.InitialFor profileMode where
  statementFuel : limits.validation=validityFuel+1
/-- Legacy all-allocation profile contract. -/
abbrev Initial := InitialFor .global
end DuplicatePrefix.GeneralBorrowPositiveConcreteWindowAcceptedCompleteInput
