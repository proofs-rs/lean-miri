import duplicate_prefix.DuplicatePrefixResidualClampedQueries
import duplicate_prefix.GeneralBorrowSifaPermissionConsistency
import duplicate_prefix.S02SifaQueryWeakening

namespace DuplicatePrefix.S02SifaResidualForeign
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false

/-- Further legal removals can only decrease a query's residual contributors. -/
theorem residual_mono (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (kind : AccessKind) (before after : List UniIndex)
    (subset : ∀ index ∈ before,index ∈ after) (query : UniIndex) :
    residualCount tree location protections kind after query ≤
      residualCount tree location protections kind before query := by
  unfold residualCount
  generalize tree.nodes.entries.toList.filter
    (GeneralBorrowExposureCardinality.contributes tree.nodes
      (GeneralBorrowExposureCardinality.effective location protections) query kind) = rows
  induction rows with
  | nil => simp
  | cons row rest ih =>
    by_cases old : row.1 ∈ before
    · have next := subset row.1 old
      simpa [List.filter_cons,old,next] using ih
    · by_cases next : row.1 ∈ after
      · simp [old,next] at ih ⊢;omega
      · simpa [List.filter_cons,old,next] using ih

private theorem unclamped_foreign_zero (root localCount : Nat) (virtual : Bool)
    (foreign : classify root localCount virtual false = some .ForeignAccess) : localCount = 0 := by
  cases virtual <;>
    by_cases zero : localCount = 0 <;>
    by_cases rootZero : root = 0 <;>
    by_cases equal : root = localCount <;>
    by_cases plusEqual : root + 1 = localCount <;>
    simp_all [classify]

/-- A certified Foreign entry stays Foreign through any larger legal removal
mask. Clamped queries use the original same-mask authorization; unclamped
queries use the monotone zero local count and the same-mask nonabsence. -/
theorem foreign_persists (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (position : Nat) (maximum : Option BorTag)
    (area : UniIndex → Prop)
    (old : Authorization tree location protections root position maximum .Write area)
    (before after : List UniIndex)
    (_legalBefore : Removal tree location protections maximum .Write before)
    (legalAfter : Removal tree location protections maximum .Write after)
    (subset : ∀ query ∈ before,query ∈ after)
    (inside : area index) (present : tree.nodes.get index = some node) (retained : index ∉ after)
    (foreign : residualRelation tree location protections root index node maximum .Write position before = some .ForeignAccess) :
    residualRelation tree location protections root index node maximum .Write position after = some .ForeignAccess := by
  cases above : aboveMaximum node maximum with
  | true =>
    exact DuplicatePrefixResidualClampedQueries.retained_foreign tree location protections
      root index node position maximum .Write area old after legalAfter inside present retained above
  | false =>
    have beforeZero := unclamped_foreign_zero _ _ _ (by simpa only [residualRelation,above] using foreign)
    have afterZero : residualCount tree location protections .Write after index = 0 := by
      have := residual_mono tree location protections .Write before after subset index
      omega
    have same := old.queries after after legalAfter legalAfter (fun _ h => h) index node inside present retained
    have scalar := (DuplicatePrefixResidualInitialSnapshot.same_query_iff _ _ _ _).mp same
    by_cases physical : position = 0
    · have nonzero : residualCount tree location protections .Write after root ≠ 0 := by
        intro zero
        simp [residualRelation,above,classify,physical,zero,Scalar] at scalar
      simp [residualRelation,above,afterZero,classify,physical,nonzero]
    · simp [residualRelation,above,afterZero,classify,physical]

/-- A consistent cached Write skip can be weakened safely when the callback
is Foreign at both queries. Disabled stays skipped; Cell and unprotected
ReservedIM admit the real foreign transition after losing their cache skip. -/
theorem consistent_foreign_weaken (state : LocationState) (strongest : IdempotentForeignAccess)
    (held : Bool)
    (consistent : GeneralBorrowSifaPermissionConsistency.Consistent state held)
    (old : DuplicatePrefixCallbackVisitAuthorization.Authorized state .Write held
      (some .ForeignAccess) (some .ForeignAccess)) :
    DuplicatePrefixCallbackVisitAuthorization.Authorized
      {state with idempotentForeignAccess :=
        (state.idempotentForeignAccess.ensureNoStrongerThan strongest).1}
      .Write held (some .ForeignAccess) (some .ForeignAccess) := by
  rcases state with ⟨permission,accessed,cache⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases accessed <;> cases cache <;> cases strongest <;> cases held <;>
      simp_all [GeneralBorrowSifaPermissionConsistency.Consistent,
        Permission.strongestIdempotentForeignAccess,DuplicatePrefixCallbackVisitAuthorization.Authorized,
        DuplicatePrefixCallbackVisitAuthorization.entrySkip,skip,
        IdempotentForeignAccess.ensureNoStrongerThan,IdempotentForeignAccess.canSkipForeignAccess,
        IdempotentForeignAccess.isLocal,IdempotentForeignAccess.le,IdempotentForeignAccess.rank,
        IdempotentForeignAccess.fromForeign,AccessRelatedness.isForeign,Permission.isDisabled,
        Permission.isFrozen,DuplicatePrefixScalarAuthorization.Compatible,
        GeneralBorrowExposedConditionalWritePermissions.Compatible,LocationState.possible]
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases accessed <;> cases cache <;> cases strongest <;> cases held <;>
      simp_all [GeneralBorrowSifaPermissionConsistency.Consistent,
        Permission.strongestIdempotentForeignAccess,DuplicatePrefixCallbackVisitAuthorization.Authorized,
        DuplicatePrefixCallbackVisitAuthorization.entrySkip,skip,
        IdempotentForeignAccess.ensureNoStrongerThan,IdempotentForeignAccess.canSkipForeignAccess,
        IdempotentForeignAccess.isLocal,IdempotentForeignAccess.le,IdempotentForeignAccess.rank,
        IdempotentForeignAccess.fromForeign,AccessRelatedness.isForeign,Permission.isDisabled,
        Permission.isFrozen,DuplicatePrefixScalarAuthorization.Compatible,
        GeneralBorrowExposedConditionalWritePermissions.Compatible,LocationState.possible]

/-- The complete original Write query family survives scalar SIFA weakening.
Residual classification and permission consistency discharge the lost Foreign
entry-skip branch; no future access-success premise is used. -/
theorem write_query_weaken (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (position : Nat) (maximum : Option BorTag)
    (area : UniIndex → Prop)
    (old : Authorization tree location protections root position maximum .Write area)
    (before after : List UniIndex)
    (legalBefore : Removal tree location protections maximum .Write before)
    (legalAfter : Removal tree location protections maximum .Write after)
    (subset : ∀ query ∈ before,query ∈ after)
    (inside : area index) (present : tree.nodes.get index = some node) (retained : index ∉ after)
    (strongest : IdempotentForeignAccess)
    (consistent : GeneralBorrowSifaPermissionConsistency.Consistent
      ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)) :
    DuplicatePrefixCallbackVisitAuthorization.Authorized
      {((location.perms.get index).getD node.defaultLocationState) with
        idempotentForeignAccess :=
          (((location.perms.get index).getD node.defaultLocationState).idempotentForeignAccess.ensureNoStrongerThan strongest).1}
      .Write (protections.contains node.tag)
      (residualRelation tree location protections root index node maximum .Write position before)
      (residualRelation tree location protections root index node maximum .Write position after) := by
  have initial := old.queries before after legalBefore legalAfter subset index node inside present retained
  by_cases foreign : residualRelation tree location protections root index node maximum .Write position before = some .ForeignAccess
  · have exitForeign := foreign_persists tree location protections root index node position maximum area old
      before after legalBefore legalAfter subset inside present retained foreign
    rw [foreign,exitForeign] at initial ⊢
    exact consistent_foreign_weaken _ strongest _ consistent initial
  · exact S02SifaQueryWeakening.authorized_weaken_of_entry_not_foreign _ strongest .Write _ _ _ foreign initial

end DuplicatePrefix.S02SifaResidualForeign
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S02SifaResidualForeign.residual_mono,
      ``DuplicatePrefix.S02SifaResidualForeign.consistent_foreign_weaken,
      ``DuplicatePrefix.S02SifaResidualForeign.write_query_weaken,
      ``DuplicatePrefix.S02SifaResidualForeign.foreign_persists] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
