import duplicate_prefix.GeneralBorrowSifaPermissionConsistency
import duplicate_prefix.DuplicatePrefixResidualSupportAuthorization

namespace DuplicatePrefix.S04ZeroReadSifaAuthorization
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixCallbackVisitAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

macro "simplify_reset" : tactic => `(tactic| simp_all [Authorized,entrySkip,skip,
  GeneralBorrowSifaPermissionConsistency.Consistent,Permission.strongestIdempotentForeignAccess,
  IdempotentForeignAccess.rank,IdempotentForeignAccess.ensureNoStrongerThan,LocationState.possible,Permission.isUnique,AccessRelatedness.isForeign,
  IdempotentForeignAccess.canSkipForeignAccess,IdempotentForeignAccess.fromForeign,
  IdempotentForeignAccess.isLocal,IdempotentForeignAccess.le,Permission.isDisabled,Permission.isFrozen,
  DuplicatePrefixScalarAuthorization.Compatible,GeneralBorrowProtectedReadCompatible.Compatible,
  GeneralBorrowExposedConditionalWritePermissions.Compatible])

/-- Weakening recorded SIFA with the actual Read threshold cannot invalidate a previously authorized
callback pair when the exit classification exists. Formed scalar consistency
excludes skips that mask a permission violation. The classification condition
must be derived from contributor/witness geometry by the caller. -/
theorem reset (state : LocationState) (kind : AccessKind) (held : Bool)
    (entry exit : Option WildcardAccessRelatedness)
    (consistent : GeneralBorrowSifaPermissionConsistency.Consistent state held)
    (authorized : Authorized state kind held entry exit) (present : exit ≠ none) :
    Authorized {state with idempotentForeignAccess := (state.idempotentForeignAccess.ensureNoStrongerThan .Read).1} kind held entry exit := by
  cases entry <;> cases exit
  all_goals try cases ‹WildcardAccessRelatedness›
  all_goals try cases ‹WildcardAccessRelatedness›
  all_goals
    rcases state with ⟨permission,accessed,sifa⟩
    cases permission with
    | ReservedFrz conflicted =>
      cases conflicted <;> cases accessed <;> cases sifa <;> cases kind <;> cases held <;>
        simplify_reset
    | Cell | ReservedIM | Unique | Frozen | Disabled =>
      cases accessed <;> cases sifa <;> cases kind <;> cases held <;> simplify_reset

/-- The original raw authorization itself rules out a missing exit query: use
its universal nested-mask requirement with the same mask twice. No extra
cutoff visibility or successful access is assumed. -/
theorem query_nonempty (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option Miri.Memory.BorTag) (kind : AccessKind)
    (support : UniIndex → Prop)
    (old : DuplicatePrefixResidualSupportAuthorization.Authorization tree location protections root position maximum kind support)
    (removed : List UniIndex)
    (legal : DuplicatePrefixResidualSupportAuthorization.Removal tree location protections maximum kind removed)
    (query : UniIndex) (node : TreeNode) (inside : support query)
    (present : tree.nodes.get query = some node) (retained : query ∉ removed) :
    DuplicatePrefixResidualSupportAuthorization.residualRelation tree location protections root query node maximum kind position removed ≠ none := by
  have same := old.queries removed removed legal legal (by intro index member;exact member)
    query node inside present retained
  intro missing
  rw [missing] at same
  simp only [Authorized,entrySkip,Bool.false_eq_true,false_or] at same
  exact same.2

/-- At every retained authorized callback node, actual Read-threshold constructor
SIFA reset is compatible with every legal pair of residual masks. The exit
nonemptiness needed by reset is derived, rather than another caller premise. -/
theorem reset_query (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option Miri.Memory.BorTag) (kind : AccessKind)
    (support : UniIndex → Prop)
    (old : DuplicatePrefixResidualSupportAuthorization.Authorization tree location protections root position maximum kind support)
    (before after : List UniIndex)
    (legalBefore : DuplicatePrefixResidualSupportAuthorization.Removal tree location protections maximum kind before)
    (legalAfter : DuplicatePrefixResidualSupportAuthorization.Removal tree location protections maximum kind after)
    (subset : ∀ index ∈ before,index ∈ after)
    (query : UniIndex) (node : TreeNode) (inside : support query)
    (present : tree.nodes.get query = some node) (retained : query ∉ after)
    (consistent : GeneralBorrowSifaPermissionConsistency.Consistent
      ((location.perms.get query).getD node.defaultLocationState) (protections.contains node.tag)) :
    Authorized {((location.perms.get query).getD node.defaultLocationState) with idempotentForeignAccess := (((location.perms.get query).getD node.defaultLocationState).idempotentForeignAccess.ensureNoStrongerThan .Read).1}
      kind (protections.contains node.tag)
      (DuplicatePrefixResidualSupportAuthorization.residualRelation tree location protections root query node maximum kind position before)
      (DuplicatePrefixResidualSupportAuthorization.residualRelation tree location protections root query node maximum kind position after) :=
  reset _ kind _ _ _ consistent
    (old.queries before after legalBefore legalAfter subset query node inside present retained)
    (query_nonempty tree location protections root position maximum kind support old after legalAfter query node inside present retained)

end DuplicatePrefix.S04ZeroReadSifaAuthorization
