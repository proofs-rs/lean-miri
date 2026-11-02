import duplicate_prefix.DuplicatePrefixConstructorNormalShape
import duplicate_prefix.GeneralBorrowFreshDefaultChild
namespace DuplicatePrefix.DuplicatePrefixDefaultConstructorNormalShape
open Miri.TreeBorrows Miri.TreeBorrows.Tree
/-- Current unprotected mutable reservations authorize local Read and Write. -/
theorem default_local_both (kind : AccessKind) :
    DuplicatePrefixScalarAuthorization.Compatible GeneralBorrowFreshDefaultChild.inside kind .LocalAccess false := by
  cases kind <;> simp [DuplicatePrefixScalarAuthorization.Compatible,GeneralBorrowProtectedReadCompatible.Compatible,
    GeneralBorrowExposedConditionalWritePermissions.Compatible,GeneralBorrowFreshDefaultChild.inside,LocationState.possible]
/-- The original source can foreign-access the unprotected fresh reservation. -/
theorem default_foreign_both (kind : AccessKind) :
    DuplicatePrefixScalarAuthorization.Compatible GeneralBorrowFreshDefaultChild.inside kind .ForeignAccess false := by
  cases kind <;> simp [DuplicatePrefixScalarAuthorization.Compatible,GeneralBorrowProtectedReadCompatible.Compatible,
    GeneralBorrowExposedConditionalWritePermissions.Compatible,GeneralBorrowFreshDefaultChild.inside,LocationState.possible]
end DuplicatePrefix.DuplicatePrefixDefaultConstructorNormalShape
