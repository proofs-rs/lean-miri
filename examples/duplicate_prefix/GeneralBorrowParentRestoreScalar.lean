import duplicate_prefix.DuplicatePrefixScalarAuthorization
namespace DuplicatePrefix.GeneralBorrowParentRestoreScalar
open Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Exact scalar compatibility is monotone when a protector table weakens. -/
theorem weakens (state : LocationState) (kind : AccessKind) (related : AccessRelatedness)
    (before after : Bool) (weaken : after = true → before = true)
    (old : DuplicatePrefixScalarAuthorization.Compatible state kind related before) :
    DuplicatePrefixScalarAuthorization.Compatible state kind related after := by
  cases kind <;> cases related <;> cases before <;> cases after <;>
    simp_all [DuplicatePrefixScalarAuthorization.Compatible,GeneralBorrowProtectedReadCompatible.Compatible,
      GeneralBorrowExposedConditionalWritePermissions.Compatible]

/-- A former local source becomes foreign-compatible for both kinds after its
own protector is gone; this uses its actual possible-state fact. -/
theorem foreign (state : LocationState) (held : Bool)
    (old : DuplicatePrefixScalarAuthorization.Compatible state .Read .LocalAccess held) (kind : AccessKind) :
    DuplicatePrefixScalarAuthorization.Compatible state kind .ForeignAccess false := by
  cases kind <;> exact ⟨old.1,by simp⟩

/-- Protected local Write excludes conflicted reservations, exactly the case
whose strongest local access would change on protector removal. -/
theorem strongest_stable (state : LocationState)
    (write : DuplicatePrefixScalarAuthorization.Compatible state .Write .LocalAccess true) :
    state.permission.strongestAllowedLocalAccess false = state.permission.strongestAllowedLocalAccess true := by
  have excluded : state.permission ≠ .ReservedFrz true := write.2.2.2 rfl
  cases permission : state.permission with
  | ReservedFrz conflicted => cases conflicted <;> simp_all [Permission.strongestAllowedLocalAccess]
  | Cell | ReservedIM | Unique | Frozen | Disabled => rfl
end DuplicatePrefix.GeneralBorrowParentRestoreScalar
