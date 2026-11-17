import duplicate_prefix.DuplicatePrefixResidualSupportSnapshotBridge

namespace DuplicatePrefix.DuplicatePrefixResidualInitialSnapshot
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false

/-- With the same entry and exit classification, the two-query contract
reduces exactly to the single-snapshot scalar table, including real skips. -/
theorem same_query_iff (state : LocationState) (kind : AccessKind) (held : Bool)
    (query : Option WildcardAccessRelatedness) :
    DuplicatePrefixCallbackVisitAuthorization.Authorized state kind held query query ↔
      Scalar state kind held query := by
  cases query with
  | none => simp [DuplicatePrefixCallbackVisitAuthorization.Authorized,
      DuplicatePrefixCallbackVisitAuthorization.entrySkip, Scalar]
  | some related =>
    cases related with
    | EitherAccess => simp [DuplicatePrefixCallbackVisitAuthorization.Authorized,
        DuplicatePrefixCallbackVisitAuthorization.entrySkip, Scalar]
    | LocalAccess =>
      cases cached : skip state kind .LocalAccess <;>
        simp [DuplicatePrefixCallbackVisitAuthorization.Authorized,
          DuplicatePrefixCallbackVisitAuthorization.entrySkip, Scalar, ExactQuery, cached]
    | ForeignAccess =>
      cases cached : skip state kind .ForeignAccess <;>
        simp [DuplicatePrefixCallbackVisitAuthorization.Authorized,
          DuplicatePrefixCallbackVisitAuthorization.entrySkip, Scalar, ExactQuery, cached]

/-- The residual-pair contract supplies the actual initial snapshot. This
uses the empty legal removal sets and genuine cache coherence; it does not
assume the subsequent visitor completes or that its cache remains unchanged. -/
theorem snapshot (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) (kind : AccessKind)
    (support : UniIndex → Prop)
    (authorization : Authorization tree location protections root rootPosition maximum kind support)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536) :
    Snapshot tree location protections root rootPosition maximum kind support := by
  refine ⟨?_, authorization.witness⟩
  intro index node included present
  have empty := empty_removal tree location protections maximum kind
  have authorized := authorization.queries [] [] empty empty (by intro query member; cases member)
    index node included present (by simp)
  rw [initial_relation tree location protections root index node maximum kind rootPosition coherent short] at authorized
  exact (same_query_iff _ _ _ _).mp authorized

end DuplicatePrefix.DuplicatePrefixResidualInitialSnapshot
