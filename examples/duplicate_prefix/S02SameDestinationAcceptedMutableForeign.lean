import duplicate_prefix.S02FrozenOutside
namespace DuplicatePrefix.S02SameDestinationAcceptedMutableForeign
open Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 200000
/-- A new lazy reservation has not been accessed outside its construction range. -/
theorem foreign (sifa : IdempotentForeignAccess) (kind : AccessKind) (held : Bool) :
    DuplicatePrefixScalarAuthorization.Compatible ⟨.ReservedFrz false,false,sifa⟩ kind .ForeignAccess held := by
  cases kind <;> cases held <;>
    simp [DuplicatePrefixScalarAuthorization.Compatible,GeneralBorrowProtectedReadCompatible.Compatible,
      GeneralBorrowExposedConditionalWritePermissions.Compatible,LocationState.possible,Permission.isUnique]
theorem query (sifa : IdempotentForeignAccess) (kind : AccessKind) (held : Bool) :
    DuplicatePrefixCallbackVisitAuthorization.Authorized ⟨.ReservedFrz false,false,sifa⟩ kind held
      (some .ForeignAccess) (some .ForeignAccess) := by
  cases sifa <;> cases kind <;> cases held <;>
    simp [DuplicatePrefixCallbackVisitAuthorization.Authorized,DuplicatePrefixCallbackVisitAuthorization.entrySkip,
      DuplicatePrefixCallbackAuthorization.skip,DuplicatePrefixScalarAuthorization.Compatible,
      GeneralBorrowProtectedReadCompatible.Compatible,GeneralBorrowExposedConditionalWritePermissions.Compatible,
      LocationState.possible,Permission.isUnique,IdempotentForeignAccess.canSkipForeignAccess,
      IdempotentForeignAccess.fromForeign,AccessRelatedness.isForeign,Permission.isDisabled,Permission.isFrozen]
end DuplicatePrefix.S02SameDestinationAcceptedMutableForeign
