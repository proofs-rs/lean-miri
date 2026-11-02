import duplicate_prefix.S05SemanticReadEffects
import duplicate_prefix.GeneralBorrowSnapshotReadTransfer
import duplicate_prefix.OrdinaryBorrowAuthorityBridge

/-! Raw mutable-right extraction from existing Read endpoint information.
These are scalar proof-output consumers, not new caller conditions or an
alternative visitor. The production DFS derives transfer and effect facts. -/
namespace DuplicatePrefix.S05ReadRawAuthorityEndpoint
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open OrdinaryBorrowAuthority DuplicatePrefixCallbackAuthorization
open DuplicatePrefixCallbackVisitAuthorization GeneralBorrowSnapshotReadTransfer
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem local_right (before after : LocationState) (held : Bool)
    (query : Option WildcardAccessRelatedness)
    (initial : LocalWrite before held) (notForeign : query ≠ some .ForeignAccess)
    (transfer : Transfer query before after held) : LocalWrite after held := by
  have guards : QueryGuards query (some .LocalAccess) (some .LocalAccess) := by
    cases query with
    | none => trivial
    | some related => cases related <;> simp_all [QueryGuards,DuplicatePrefixReadWriteScalarAuthorization.Guards]
  have old : Authorized before .Write held (some .LocalAccess) (some .LocalAccess) := by
    exact ⟨initial.1,Or.inr ⟨rfl,initial⟩⟩
  have current := transfer _ _ guards old
  exact (current.2.resolve_left (by simp [entrySkip,skip,AccessRelatedness.isForeign])).2

private theorem cell_of_read_information (before after : LocationState)
    (cell : before.permission = .Cell)
    (effects : S05SemanticReadEffects.Related before after true)
    (readFrame : (after.permission.strongestAllowedLocalAccess true).allows .Read =
      (before.permission.strongestAllowedLocalAccess true).allows .Read) : after.permission = .Cell := by
  have bound : GeneralBorrowSifaPermissionConsistency.Consistent {before with idempotentForeignAccess := .Write} true := by
    exact ⟨.Write,by simp [cell,Permission.strongestIdempotentForeignAccess],Nat.le_refl _⟩
  have afterBound := S05SemanticReadEffects.transport before after true .Write effects bound
  obtain ⟨strength,table,large⟩ := afterBound
  cases permission : after.permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases strength <;>
      simp_all [GeneralBorrowSifaPermissionConsistency.Consistent,Permission.strongestIdempotentForeignAccess,IdempotentForeignAccess.rank]
  | Cell => rfl
  | ReservedIM | Unique | Frozen | Disabled =>
    cases strength <;> simp_all [Permission.strongestIdempotentForeignAccess,IdempotentForeignAccess.rank,
      Permission.strongestAllowedLocalAccess,WildcardAccessLevel.allows]

private theorem foreign_skip_cases (state : LocationState)
    (right : ForeignWrite state true)
    (consistent : GeneralBorrowSifaPermissionConsistency.Consistent state true) :
    state.permission = .Cell ∨ state.permission = .Disabled ∨ skip state .Write .ForeignAccess = false := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | Cell => exact Or.inl rfl
  | Disabled => exact Or.inr (Or.inl rfl)
  | ReservedFrz conflicted =>
    right;right
    cases conflicted <;> cases accessed <;> cases sifa <;>
      simp_all [ForeignWrite,GeneralBorrowSifaPermissionConsistency.Consistent,
        Permission.strongestIdempotentForeignAccess,IdempotentForeignAccess.rank,skip,
        IdempotentForeignAccess.canSkipForeignAccess,IdempotentForeignAccess.fromForeign,
        IdempotentForeignAccess.isLocal,IdempotentForeignAccess.le,
        Permission.isDisabled,Permission.isFrozen,AccessRelatedness.isForeign]
  | ReservedIM | Unique | Frozen =>
    right;right
    cases accessed <;> cases sifa <;>
      simp_all [ForeignWrite,GeneralBorrowSifaPermissionConsistency.Consistent,
        LocationState.possible,Permission.isUnique,Permission.strongestIdempotentForeignAccess,
        IdempotentForeignAccess.rank,skip,IdempotentForeignAccess.canSkipForeignAccess,
        IdempotentForeignAccess.fromForeign,IdempotentForeignAccess.isLocal,IdempotentForeignAccess.le,
        Permission.isDisabled,Permission.isFrozen,AccessRelatedness.isForeign]

theorem foreign_right (before after : LocationState) (held : Bool)
    (query : Option WildcardAccessRelatedness)
    (initial : ForeignWrite before held) (notLocal : query ≠ some .LocalAccess)
    (transfer : Transfer query before after held)
    (effects : S05SemanticReadEffects.Related before after held)
    (readFrame : (after.permission.strongestAllowedLocalAccess held).allows .Read =
      (before.permission.strongestAllowedLocalAccess held).allows .Read)
    (consistent : GeneralBorrowSifaPermissionConsistency.Consistent before held)
    (possible : after.possible = true) : ForeignWrite after held := by
  cases held with
  | false => exact ⟨possible,by simp⟩
  | true =>
    rcases foreign_skip_cases before initial consistent with cell | disabled | notSkipped
    · exact ⟨possible,fun _ => Or.inl (cell_of_read_information before after cell effects readFrame)⟩
    · have fields := effects.disabled disabled
      have dormant : before.accessed = false := by
        rcases initial.2 rfl with cell | dormant
        · simp [disabled] at cell
        · exact dormant.2
      exact ⟨possible,fun _ => Or.inr ⟨by simp [fields.1],fields.2.trans dormant⟩⟩
    · have guards : QueryGuards query (some .EitherAccess) (some .ForeignAccess) := by
        cases query with
        | none => trivial
        | some related => cases related <;> simp_all [QueryGuards,DuplicatePrefixReadWriteScalarAuthorization.Guards]
      have old : Authorized before .Write true (some .EitherAccess) (some .ForeignAccess) :=
        ⟨initial.1,Or.inr ⟨notSkipped,initial⟩⟩
      have current := transfer _ _ guards old
      exact (current.2.resolve_left (by simp [entrySkip])).2

end DuplicatePrefix.S05ReadRawAuthorityEndpoint

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05ReadRawAuthorityEndpoint." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved Read authority endpoint dependency {dependency}"
