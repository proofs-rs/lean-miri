import duplicate_prefix.DuplicatePrefixResidualSupportAuthorization

namespace DuplicatePrefix.DuplicatePrefixResidualSupportSnapshotBridge
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization

/-- A single unchanged query needs no stronger permission condition than the
exact snapshot table. The entry skip is respected before any exit transition. -/
theorem same_query (state : LocationState) (kind : AccessKind) (held : Bool)
    (query : Option WildcardAccessRelatedness) (scalar : Scalar state kind held query) :
    DuplicatePrefixCallbackVisitAuthorization.Authorized state kind held query query := by
  cases query with
  | none => exact False.elim scalar
  | some related =>
    cases related with
    | EitherAccess => exact ⟨scalar, .inr trivial⟩
    | LocalAccess =>
      refine ⟨scalar.1, ?_⟩
      cases skipped : skip state kind .LocalAccess with
      | true => exact .inl skipped
      | false => exact .inr ⟨rfl, scalar.2.resolve_left (by simp [skipped])⟩
    | ForeignAccess =>
      refine ⟨scalar.1, ?_⟩
      cases skipped : skip state kind .ForeignAccess with
      | true => exact .inl skipped
      | false => exact .inr ⟨rfl, scalar.2.resolve_left (by simp [skipped])⟩

theorem scalar_possible (state : LocationState) (kind : AccessKind) (held : Bool)
    (query : Option WildcardAccessRelatedness) (scalar : Scalar state kind held query) :
    state.possible = true := by
  cases query with
  | none => exact False.elim scalar
  | some related => cases related <;> first | exact scalar.1 | exact scalar

/-- A genuine eligible witness cannot be above the selected-root tag cutoff.
This fact uses the raw witness data, not a successful callback. -/
theorem witness_below_maximum (location : LocationTree) (protections : ProtectedTags)
    (index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (kind : AccessKind)
    (witness : Supports location protections index node maximum kind) :
    aboveMaximum node maximum = false := by
  have bound := witness.2.2
  cases maximum with
  | none => rfl
  | some maximum =>
    simp only [Option.isNone_some, Option.any_some, Bool.false_or, decide_eq_true_eq] at bound
    simp [aboveMaximum, UInt64.not_lt, bound]

/-- Every admissible removal set retains a source-eligible exposed witness.
This is a finite-set statement only; actual node visitation and permission
preservation must still be proved when connecting the visitor to this model. -/
theorem witness_retained (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (maximum : Option BorTag) (kind : AccessKind) (removed : List UniIndex)
    (legal : Removal tree location protections maximum kind removed)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
    (witness : Supports location protections index node maximum kind) : index ∉ removed := by
  apply nondroppable_retained tree location protections maximum kind removed legal index node present
  have below := witness_below_maximum location protections index node maximum kind witness
  cases kind <;> simp [removable, below]

/-- The residual-pair specification is supplied by a raw snapshot whenever
the contribution-removal policy admits only the empty set. This is a contract
bridge, not a claim that the actual traversal preserves the count model. -/
theorem of_snapshot (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) (kind : AccessKind)
    (support : UniIndex → Prop)
    (snapshot : Snapshot tree location protections root rootPosition maximum kind support)
    (rooted : support root)
    (present : ∀ index, support index → ∃ node, tree.nodes.get index = some node)
    (children : ∀ index node, support index → tree.nodes.get index = some node →
      ∀ child ∈ node.children.toList, support child)
    (covers : ∀ index, support index → GeneralBorrowExposureCardinality.Covers tree.nodes root index)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536)
    (noRemovals : ∀ removed, Removal tree location protections maximum kind removed → removed = []) :
    Authorization tree location protections root rootPosition maximum kind support := by
  refine ⟨rooted, present, children, covers, ?_, ?_, snapshot.witness⟩
  · intro index node inside lookup
    exact scalar_possible _ _ _ _ (snapshot.scalar index node inside lookup)
  · intro before after legalBefore legalAfter subset index node inside lookup notRemoved
    have beforeEmpty := noRemovals before legalBefore
    have afterEmpty := noRemovals after legalAfter
    subst before
    subst after
    rw [initial_relation tree location protections root index node maximum kind rootPosition coherent short]
    exact same_query _ _ _ _ (snapshot.scalar index node inside lookup)

end DuplicatePrefix.DuplicatePrefixResidualSupportSnapshotBridge
