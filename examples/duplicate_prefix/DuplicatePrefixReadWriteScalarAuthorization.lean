import duplicate_prefix.GeneralBorrowExposedConditionalReadPermissions
import duplicate_prefix.DuplicatePrefixCallbackVisitAuthorization
namespace DuplicatePrefix.DuplicatePrefixReadWriteScalarAuthorization
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixCallbackVisitAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-- Same-state Read classification constrains each masked Write query. The
finite contributor-set guard supplies these facts for both removal snapshots. -/
def Guards (read : AccessRelatedness) (entry exit : Option WildcardAccessRelatedness) : Prop :=
  (read = .LocalAccess → (entry = some .LocalAccess ∨ entry = none) ∧ (exit = some .LocalAccess ∨ exit = none)) ∧
  (read = .ForeignAccess → entry ≠ some .LocalAccess ∧ exit ≠ some .LocalAccess)

macro "simplify_transfer" : tactic => `(tactic| simp_all [Guards,Authorized,entrySkip,skip,
  DuplicatePrefixScalarAuthorization.Compatible,GeneralBorrowProtectedReadCompatible.Compatible,
  GeneralBorrowExposedConditionalWritePermissions.Compatible,GeneralBorrowEvents.Scheduled,
  LocationState.possible,Permission.isUnique,Permission.isDisabled,Permission.isFrozen,
  AccessRelatedness.isForeign,IdempotentForeignAccess.fromForeign,IdempotentForeignAccess.fromAccessAndRelatedness,
  IdempotentForeignAccess.canSkipForeignAccess,IdempotentForeignAccess.isLocal,IdempotentForeignAccess.le,
  IdempotentForeignAccess.rank,IdempotentForeignAccess.recordNew,IdempotentForeignAccess.max])
/-- Scalar extraction for the real successful Read branch. Scheduling excludes
an old Write-foreign skip at a foreign Read; local Reads use the masked query
guard instead. No residual-count simulation is asserted by this local lemma. -/
theorem actual_read_preserves (state recorded next : LocationState) (delta : PermTransition)
    (read : AccessRelatedness) (held : Bool) (entry exit : Option WildcardAccessRelatedness)
    (readCompatible : GeneralBorrowProtectedReadCompatible.Compatible state read held)
    (scheduled : GeneralBorrowEvents.Scheduled state .Read read)
    (writeAuthorized : Authorized state .Write held entry exit) (guards : Guards read entry exit)
    (record : state.recordNewAccess .Read read = .Recorded recorded)
    (access : recorded.performAccess .Read read held = .Success next delta) :
    Authorized next .Write held entry exit := by
  have recordedEq : recorded = {state with idempotentForeignAccess :=
      (IdempotentForeignAccess.recordNew state.idempotentForeignAccess
        (IdempotentForeignAccess.fromAccessAndRelatedness .Read read))} := by
    simpa [LocationState.recordNewAccess, GeneralBorrowEvents.scheduled_recurse _ _ _ scheduled] using record.symm
  subst recorded
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;>
      cases accessed <;> cases sifa <;> cases held <;> cases read <;>
      cases entry <;> (try (rename_i entryRelated; cases entryRelated)) <;> cases exit <;> (try (rename_i exitRelated; cases exitRelated)) <;> simplify_transfer
    all_goals
      change LocationState.AccessResult.Success _ _ = .Success next delta at access
      cases access
      simplify_transfer
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases accessed <;> cases sifa <;> cases held <;> cases read <;>
      cases entry <;> (try (rename_i entryRelated; cases entryRelated)) <;> cases exit <;> (try (rename_i exitRelated; cases exitRelated)) <;> simplify_transfer
    all_goals
      change LocationState.AccessResult.Success _ _ = .Success next delta at access
      cases access
      simplify_transfer

/-- Compatibility, scheduling and the masked cross-kind guards derive the
actual Read record/access and preservation of the old Write query-pair
Authorized contract. Successful operations occur only in the conclusion. -/
theorem visit (state : LocationState) (read : AccessRelatedness) (held : Bool)
    (entry exit : Option WildcardAccessRelatedness)
    (readCompatible : GeneralBorrowProtectedReadCompatible.Compatible state read held)
    (scheduled : GeneralBorrowEvents.Scheduled state .Read read)
    (writeAuthorized : Authorized state .Write held entry exit) (guards : Guards read entry exit) :
    ∃ recorded next delta, state.recordNewAccess .Read read = .Recorded recorded ∧
      recorded.performAccess .Read read held = .Success next delta ∧
      Authorized next .Write held entry exit := by
  obtain ⟨recorded,next,delta,record,access,_,_⟩ :=
    GeneralBorrowExposedConditionalReadPermissions.visit state read held readCompatible scheduled
  exact ⟨recorded,next,delta,record,access,
    actual_read_preserves state recorded next delta read held entry exit readCompatible scheduled writeAuthorized guards record access⟩
end DuplicatePrefix.DuplicatePrefixReadWriteScalarAuthorization
