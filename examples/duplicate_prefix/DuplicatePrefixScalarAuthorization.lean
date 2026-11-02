import duplicate_prefix.GeneralBorrowExposedConditionalWritePermissions

namespace DuplicatePrefix.DuplicatePrefixScalarAuthorization
open Miri.TreeBorrows Miri.TreeBorrows.Tree

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Data-only permission/protector/accessed conditions for one exact scalar
transition. Read and Write deliberately use different foreign-access rules.
The actual visitor can also skip a node; this is not whole-visitor validity. -/
def Compatible (state : LocationState) (kind : AccessKind)
    (related : AccessRelatedness) (held : Bool) : Prop :=
  match kind with
  | .Read => GeneralBorrowProtectedReadCompatible.Compatible state related held
  | .Write => GeneralBorrowExposedConditionalWritePermissions.Compatible state related held

/-- On possible initial states the raw table exactly characterizes the actual
scalar transition, rather than merely choosing an unnecessarily strong subset.
The successful operation occurs only in this theorem's conclusion/equivalence;
it is not a field of the authorization definition. -/
theorem compatible_iff (state : LocationState) (kind : AccessKind)
    (related : AccessRelatedness) (held : Bool) (possible : state.possible = true) :
    Compatible state kind related held ↔
      ∃ next delta, state.performAccess kind related held = .Success next delta := by
  rcases state with ⟨permission, accessed, sifa⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases accessed <;> cases sifa <;> cases kind <;> cases related <;> cases held <;>
      simp [Compatible, GeneralBorrowProtectedReadCompatible.Compatible,
        GeneralBorrowExposedConditionalWritePermissions.Compatible,
        LocationState.possible, Permission.isUnique] at possible ⊢ <;>
      first | exact ⟨_, _, rfl⟩ | (intro next delta equal; cases equal)
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases accessed <;> cases sifa <;> cases kind <;> cases related <;> cases held <;>
      simp [Compatible, GeneralBorrowProtectedReadCompatible.Compatible,
        GeneralBorrowExposedConditionalWritePermissions.Compatible,
        LocationState.possible, Permission.isUnique] at possible ⊢ <;>
      first | exact ⟨_, _, rfl⟩ | (intro next delta equal; cases equal)

end DuplicatePrefix.DuplicatePrefixScalarAuthorization
