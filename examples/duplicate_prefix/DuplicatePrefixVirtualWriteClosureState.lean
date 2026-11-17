import duplicate_prefix.DuplicatePrefixResidualSavedWritePost
import duplicate_prefix.DuplicatePrefixResidualWriteSkip
import duplicate_prefix.DuplicatePrefixResidualComposition
import duplicate_prefix.DuplicatePrefixResidualInitialSnapshot
namespace DuplicatePrefix.DuplicatePrefixVirtualWriteClosureState
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization DuplicatePrefixResidualCountModel
open GeneralBorrowWildcardVirtualLeaf (effective materialized)
open GeneralBorrowExposedNonleafState (updated updated_other)
open GeneralBorrowExposedConditionalWritePermissions (Compatible support)
open DuplicatePrefixResidualReadWriteEffects (Origin)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

/-- Scalar extraction for a real foreign Write. Surviving supporting
permissions are unchanged; all successors are foreign-compatible. -/
theorem foreign_effects (state next : LocationState) (held : Bool) (delta : PermTransition)
    (actual : state.performAccess .Write .ForeignAccess held = .Success next delta) :
    Compatible next .ForeignAccess held ∧
      (support state held = false → support next held = false) ∧
      (support next held = true → next.permission = state.permission) := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases accessed <;> cases sifa <;> cases held
    all_goals cases actual
    all_goals simp_all [Compatible,LocationState.possible,Permission.isUnique,AccessRelatedness.isForeign,support,
      GeneralBorrowExposureCardinality.supports,Permission.strongestAllowedLocalAccess,GeneralBorrowExposureAncestorFold.supportsWrite]
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases accessed <;> cases sifa <;> cases held
    all_goals cases actual
    all_goals simp_all [Compatible,LocationState.possible,Permission.isUnique,AccessRelatedness.isForeign,support,
      GeneralBorrowExposureCardinality.supports,Permission.strongestAllowedLocalAccess,GeneralBorrowExposureAncestorFold.supportsWrite]

theorem residual_decreases (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (before after : List UniIndex) (subset : ∀ index ∈ before, index ∈ after) (query : UniIndex) :
    residualCount tree initial protections .Write after query ≤ residualCount tree initial protections .Write before query := by
  have equality (items : List (UniIndex × TreeNode)) : items.filter (fun row => !after.contains row.1) =
      (items.filter (fun row => !before.contains row.1)).filter (fun row => !after.contains row.1) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro row member
    by_cases earlier : row.1 ∈ before
    · have later := subset row.1 earlier
      simp [earlier,later]
    · simp [earlier]
  unfold residualCount
  rw [equality]
  exact List.length_filter_le _ _

/-- Once exact Foreign, virtual classification remains Foreign as support
masks grow: either the tag clamp applies or the local Write count is zero. -/
theorem foreign_persists (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (position : Nat)
    (virtual : position ≠ 0) (covers : GeneralBorrowExposureCardinality.Covers tree.nodes root index)
    (before after : List UniIndex) (subset : ∀ query ∈ before, query ∈ after)
    (foreign : residualRelation tree initial protections root index node maximum .Write position before = some .ForeignAccess) :
    residualRelation tree initial protections root index node maximum .Write position after = some .ForeignAccess := by
  have beforeBound := DuplicatePrefixResidualWriteSkip.residual_dominates tree initial protections before root index covers
  have afterBound := DuplicatePrefixResidualWriteSkip.residual_dominates tree initial protections after root index covers
  have decrease := residual_decreases tree initial protections before after subset index
  have virtualEq : (position != 0) = true := by simp [virtual]
  simpa only [residualRelation,virtualEq] using DuplicatePrefixResidualWriteSkip.virtual_foreign_persists _ _ _ _ _ beforeBound afterBound decrease
    (by simpa only [residualRelation,virtualEq] using foreign)

/-- Unchanged effective nodes retain their old raw queries. Changed nodes
have a foreign-compatible scalar state and a permanently Foreign query. -/
def Safe (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (removed : List UniIndex)
    (area : UniIndex → Prop) : Prop :=
  ∀ index node, area index → tree.nodes.get index = some node →
    effective current index node = effective initial index node ∨
      Compatible (effective current index node) .ForeignAccess (protections.contains node.tag) ∧
      residualRelation tree initial protections root index node maximum .Write position removed = some .ForeignAccess

theorem safe_initial (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (area : UniIndex → Prop) :
    Safe tree initial initial protections root position maximum [] area := by
  intro index node included present
  exact .inl rfl

/-- Actual Write action preserves global Origin and the virtual Safe table.
Action equations are intermediate output certificates of the raw visitor. -/
theorem action (tree : BorrowTree) (initial current after : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (position : Nat)
    (virtual : position ≠ 0) (area : UniIndex → Prop)
    (covers : ∀ query, area query → GeneralBorrowExposureCardinality.Covers tree.nodes root query)
    (removed afterRemoved : List UniIndex)
    (matching : Matches tree initial current protections .Write removed)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree current protections)
    (short : tree.nodes.size < 65536) (present : tree.nodes.get index = some node) (inside : area index)
    (origin : Origin tree initial current protections)
    (safe : Safe tree initial current protections root position maximum removed area)
    (operation : DuplicatePrefixResidualWritePost.Action tree current protections root index node maximum position removed after afterRemoved) :
    Origin tree initial after protections ∧ Safe tree initial after protections root position maximum afterRemoved area := by
  have subset := DuplicatePrefixResidualSavedWritePost.action_mono tree current protections root index node maximum position removed after afterRemoved operation
  rcases operation with ⟨classified,same,sameMask⟩ | ⟨exact,recorded,next,delta,classified,record,actual,same,sameMask⟩
  · subst after
    subst afterRemoved
    refine ⟨DuplicatePrefixResidualReadWriteEffects.materialized_origin tree initial current protections origin index node present,?_⟩
    intro query queryNode included found
    rw [GeneralBorrowExposedVirtualSchedule.materialized_effective tree current index node present query queryNode found]
    exact safe query queryNode included found
  · subst after
    have raw := (relation_matches tree initial current protections .Write removed matching coherent short root index node maximum position).symm.trans classified
    have foreignExact : exact = .ForeignAccess := by
      cases exact with
      | ForeignAccess => rfl
      | LocalAccess =>
        have bound := DuplicatePrefixResidualWriteSkip.residual_dominates tree initial protections removed root index (covers index inside)
        simp only [residualRelation,show (position != 0) = true by simp [virtual]] at raw
        rw [DuplicatePrefixResidualWriteSkip.classify_virtual _ _ _ bound] at raw
        split at raw <;> cases raw
    subst exact
    obtain ⟨good,noGain,preserved⟩ := foreign_effects recorded next (protections.contains node.tag) delta actual
    have oldPermission := GeneralBorrowEventTransitionMetadata.record_permission _ _ .Write .ForeignAccess record
    have oldNoGain : support (effective current index node) (protections.contains node.tag) = false → support next (protections.contains node.tag) = false := by
      simpa only [support,oldPermission] using noGain
    have oldPreserved : support next (protections.contains node.tag) = true → next.permission = (effective current index node).permission := by
      intro supported
      exact (preserved supported).trans oldPermission
    refine ⟨DuplicatePrefixResidualReadWriteEffects.updated_origin tree initial current protections origin index node present recorded next delta oldNoGain oldPreserved,?_⟩
    intro query queryNode included found
    by_cases same : query = index
    · subst query
      have nodeEq : queryNode = node := Option.some.inj (found.symm.trans present)
      subst queryNode
      right
      simp only [effective,updated,GeneralBorrowWildcardSubtreeState.write_same,Option.getD_some]
      exact ⟨good,foreign_persists tree initial protections root index node maximum position virtual (covers index inside) removed afterRemoved subset raw⟩
    · simp only [effective,updated_other tree current index query node protections recorded next delta same]
      rcases safe query queryNode included found with unchanged | ⟨compatible,foreign⟩
      · exact .inl unchanged
      · exact .inr ⟨compatible,foreign_persists tree initial protections root query queryNode maximum position virtual (covers query included) removed afterRemoved subset foreign⟩
end DuplicatePrefix.DuplicatePrefixVirtualWriteClosureState
