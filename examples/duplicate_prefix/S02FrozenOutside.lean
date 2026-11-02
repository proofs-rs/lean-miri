import duplicate_prefix.S02ConstructorCallbackForeign

namespace DuplicatePrefix.S02FrozenOutside
open Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 200000

/-- A new shared child's lazy outside state accepts either foreign access,
including when the shared helper has a registered protector. -/
theorem foreign (kind : AccessKind) (held : Bool) :
    DuplicatePrefixScalarAuthorization.Compatible ⟨.Frozen,false,.Read⟩ kind .ForeignAccess held := by
  cases kind <;> cases held <;>
    simp [DuplicatePrefixScalarAuthorization.Compatible,GeneralBorrowProtectedReadCompatible.Compatible,
      GeneralBorrowExposedConditionalWritePermissions.Compatible,LocationState.possible,Permission.isUnique]

/-- Real foreign callback pairs are authorized in the new lazy Frozen row;
Read may skip while Write recurses and may disable the inactive child. -/
theorem query (kind : AccessKind) (held : Bool) :
    DuplicatePrefixCallbackVisitAuthorization.Authorized ⟨.Frozen,false,.Read⟩ kind held
      (some .ForeignAccess) (some .ForeignAccess) := by
  cases kind <;> cases held <;>
    simp [DuplicatePrefixCallbackVisitAuthorization.Authorized,DuplicatePrefixCallbackVisitAuthorization.entrySkip,
      DuplicatePrefixCallbackAuthorization.skip,DuplicatePrefixScalarAuthorization.Compatible,
      GeneralBorrowProtectedReadCompatible.Compatible,GeneralBorrowExposedConditionalWritePermissions.Compatible,
      LocationState.possible,Permission.isUnique,IdempotentForeignAccess.canSkipForeignAccess,
      IdempotentForeignAccess.fromForeign,AccessRelatedness.isForeign,Permission.isDisabled,Permission.isFrozen]

end DuplicatePrefix.S02FrozenOutside

open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S02FrozenOutside.foreign,``DuplicatePrefix.S02FrozenOutside.query] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
