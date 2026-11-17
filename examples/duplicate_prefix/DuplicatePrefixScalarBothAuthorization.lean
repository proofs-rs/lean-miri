import duplicate_prefix.DuplicatePrefixScalarAuthorization
import duplicate_prefix.GeneralBorrowPermissions

namespace DuplicatePrefix.DuplicatePrefixScalarBothAuthorization
open Miri.TreeBorrows Miri.TreeBorrows.Tree

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Both exact scalar capabilities at the same relation and protector state.
This contains only initial permission data, not a successful access premise. -/
def Both (state : LocationState) (related : AccessRelatedness) (held : Bool) : Prop :=
  DuplicatePrefixScalarAuthorization.Compatible state .Read related held ∧
  DuplicatePrefixScalarAuthorization.Compatible state .Write related held

/-- Exact comparison with the older ownership contract. The scalar tables
also admit a protected local ReservedIM node; no such state is silently
excluded by this contract. -/
theorem both_iff_owned_or_local_reserved (state : LocationState)
    (related : AccessRelatedness) (held : Bool) :
    Both state related held ↔ GeneralBorrowPermissions.Owned state related held ∨
      (state.possible = true ∧ related = .LocalAccess ∧ held = true ∧ state.permission = .ReservedIM) := by
  rcases state with ⟨permission, accessed, sifa⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases accessed <;> cases related <;> cases held <;>
      simp [Both, DuplicatePrefixScalarAuthorization.Compatible,
        GeneralBorrowProtectedReadCompatible.Compatible,
        GeneralBorrowExposedConditionalWritePermissions.Compatible,
        GeneralBorrowPermissions.Owned, GeneralBorrowPermissions.LocalOwned,
        GeneralBorrowPermissions.ForeignOwned, LocationState.possible, Permission.isUnique]
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases accessed <;> cases related <;> cases held <;>
      simp [Both, DuplicatePrefixScalarAuthorization.Compatible,
        GeneralBorrowProtectedReadCompatible.Compatible,
        GeneralBorrowExposedConditionalWritePermissions.Compatible,
        GeneralBorrowPermissions.Owned, GeneralBorrowPermissions.LocalOwned,
        GeneralBorrowPermissions.ForeignOwned, LocationState.possible, Permission.isUnique]

/-- Either actual access kind preserves both initial capabilities at the
same relation, including the real scalar permission transition. -/
theorem transition (state : LocationState) (related : AccessRelatedness) (held : Bool)
    (kind : AccessKind) (initial : Both state related held) :
    ∃ next delta, state.performAccess kind related held = .Success next delta ∧
      Both next related held := by
  rcases state with ⟨permission, accessed, sifa⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases accessed <;> cases sifa <;> cases related <;> cases held <;> cases kind <;>
      simp [Both, DuplicatePrefixScalarAuthorization.Compatible,
        GeneralBorrowProtectedReadCompatible.Compatible,
        GeneralBorrowExposedConditionalWritePermissions.Compatible,
        LocationState.possible, Permission.isUnique] at initial <;>
      (refine ⟨_, _, rfl, ?_⟩; simp [Both, DuplicatePrefixScalarAuthorization.Compatible,
        GeneralBorrowProtectedReadCompatible.Compatible,
        GeneralBorrowExposedConditionalWritePermissions.Compatible,
        LocationState.possible, Permission.isUnique, AccessRelatedness.isForeign])
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases accessed <;> cases sifa <;> cases related <;> cases held <;> cases kind <;>
      simp [Both, DuplicatePrefixScalarAuthorization.Compatible,
        GeneralBorrowProtectedReadCompatible.Compatible,
        GeneralBorrowExposedConditionalWritePermissions.Compatible,
        LocationState.possible, Permission.isUnique] at initial <;>
      (refine ⟨_, _, rfl, ?_⟩; simp [Both, DuplicatePrefixScalarAuthorization.Compatible,
        GeneralBorrowProtectedReadCompatible.Compatible,
        GeneralBorrowExposedConditionalWritePermissions.Compatible,
        LocationState.possible, Permission.isUnique, AccessRelatedness.isForeign])

/-- The real skip/record/access pipeline preserves both capabilities.
Successful record/access results are conclusions derived from initial data. -/
theorem visit (state : LocationState) (related : AccessRelatedness) (held : Bool)
    (kind : AccessKind) (initial : Both state related held) :
    state.skipIfKnownNoop kind related = .SkipSelfAndChildren ∨
      ∃ recorded next delta, state.recordNewAccess kind related = .Recorded recorded ∧
        recorded.performAccess kind related held = .Success next delta ∧
        Both next related held := by
  cases skip : state.skipIfKnownNoop kind related with
  | SkipSelfAndChildren => exact .inl rfl
  | Recurse =>
    let recorded := {state with idempotentForeignAccess := (
      IdempotentForeignAccess.recordNew state.idempotentForeignAccess
        (IdempotentForeignAccess.fromAccessAndRelatedness kind related))}
    have inherited : Both recorded related held := by
      cases related <;> exact initial
    obtain ⟨next, delta, actual, preserved⟩ := transition recorded related held kind inherited
    exact .inr ⟨recorded, next, delta,
      by simp [LocationState.recordNewAccess, skip, recorded], actual, preserved⟩

/-- Releasing a protector preserves both scalar capabilities. -/
theorem release (state : LocationState) (related : AccessRelatedness)
    (before after : Bool) (weaken : after = true → before = true)
    (initial : Both state related before) : Both state related after := by
  cases before <;> cases after <;> cases related <;>
    simp_all [Both, DuplicatePrefixScalarAuthorization.Compatible,
      GeneralBorrowProtectedReadCompatible.Compatible,
      GeneralBorrowExposedConditionalWritePermissions.Compatible]
  rcases initial with ⟨read, write⟩
  exact write.2.imp_right And.right

end DuplicatePrefix.DuplicatePrefixScalarBothAuthorization
