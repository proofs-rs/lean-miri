import duplicate_prefix.DuplicatePrefixPrimaryWriteClosureModel
namespace DuplicatePrefix.DuplicatePrefixPrimaryWriteClosureState
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization DuplicatePrefixResidualCountModel
open GeneralBorrowWildcardVirtualLeaf (effective materialized)
open GeneralBorrowExposedNonleafState (updated updated_other)
open GeneralBorrowExposedConditionalWritePermissions (Compatible support)
open DuplicatePrefixPrimaryWriteClosureModel
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

theorem local_effects (state next : LocationState) (held : Bool) (delta : PermTransition)
    (actual : state.performAccess .Write .LocalAccess held = .Success next delta) :
    Compatible next .LocalAccess held := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases accessed <;> cases held
    all_goals cases actual
    all_goals simp_all [Compatible,LocationState.possible,Permission.isUnique,AccessRelatedness.isForeign]
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases accessed <;> cases held
    all_goals cases actual
    all_goals simp_all [Compatible,LocationState.possible,Permission.isUnique,AccessRelatedness.isForeign]

def Safe (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (maximum : Option BorTag) (removed : List UniIndex) (area : UniIndex → Prop) : Prop :=
  ∀ index node, area index → tree.nodes.get index = some node →
    effective current index node = effective initial index node ∨
      ∃ related : AccessRelatedness, Compatible (effective current index node) related (protections.contains node.tag) ∧
      residualRelation tree initial protections root index node maximum .Write 0 removed = some (GeneralBorrowSnapshotReadState.wildcard related)

theorem safe_initial (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (maximum : Option BorTag) (area : UniIndex → Prop) :
    Safe tree initial initial protections root maximum [] area := by
  intro index node included present
  exact .inl rfl

theorem materialized_origin (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (maximum : Option BorTag) (origin : CutoffOrigin tree initial current protections maximum)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node) :
    CutoffOrigin tree initial (materialized current index node) protections maximum := by
  intro query queryNode found exposed above supported
  have same := GeneralBorrowExposedVirtualSchedule.materialized_effective tree current index node present query queryNode found
  change support (effective _ query queryNode) _ = true at supported
  change (effective _ query queryNode).permission = _
  rw [same] at supported ⊢
  exact origin query queryNode found exposed above supported

theorem updated_origin (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (maximum : Option BorTag) (origin : CutoffOrigin tree initial current protections maximum)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
    (recorded next : LocationState) (delta : PermTransition)
    (preserved : aboveMaximum node maximum = true → support next (protections.contains node.tag) = true →
      next.permission = (effective current index node).permission)
    (noGain : aboveMaximum node maximum = true → support (effective current index node) (protections.contains node.tag) = false →
      support next (protections.contains node.tag) = false) :
    CutoffOrigin tree initial (updated tree current index node protections recorded next delta) protections maximum := by
  intro query queryNode found exposed above supported
  change support (effective _ query queryNode) _ = true at supported
  change (effective _ query queryNode).permission = _
  by_cases same : query = index
  · subst query
    have nodeEq : queryNode = node := Option.some.inj (found.symm.trans present)
    subst queryNode
    simp only [effective,updated,GeneralBorrowWildcardSubtreeState.write_same,Option.getD_some] at supported ⊢
    have oldSupported : support (effective current index node) (protections.contains node.tag) = true := by
      cases old : support (effective current index node) (protections.contains node.tag)
      · rw [noGain above old] at supported; cases supported
      · rfl
    exact (preserved above supported).trans (origin index node present exposed above oldSupported)
  · simp only [effective,updated_other tree current index query node protections recorded next delta same] at supported ⊢
    exact origin query queryNode found exposed above supported

theorem action (tree : BorrowTree) (initial current after : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (area : UniIndex → Prop)
    (old : Authorization tree initial protections root 0 maximum .Write area)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (removed afterRemoved : List UniIndex)
    (legalAfter : Removal tree initial protections maximum .Write afterRemoved)
    (matching : Matches tree initial current protections .Write removed)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree current protections)
    (short : tree.nodes.size < 65536) (present : tree.nodes.get index = some node) (inside : area index)
    (origin : CutoffOrigin tree initial current protections maximum)
    (safe : Safe tree initial current protections root maximum removed area)
    (operation : DuplicatePrefixResidualWritePost.Action tree current protections root index node maximum 0 removed after afterRemoved) :
    CutoffOrigin tree initial after protections maximum ∧ Safe tree initial after protections root maximum afterRemoved area := by
  have subset := DuplicatePrefixResidualSavedWritePost.action_mono tree current protections root index node maximum 0 removed after afterRemoved operation
  have persist (query : UniIndex) (queryNode : TreeNode) (included : area query) (found : tree.nodes.get query = some queryNode)
      (related : AccessRelatedness)
      (classified : residualRelation tree initial protections root query queryNode maximum .Write 0 removed = some (GeneralBorrowSnapshotReadState.wildcard related)) :
      residualRelation tree initial protections root query queryNode maximum .Write 0 afterRemoved = some (GeneralBorrowSnapshotReadState.wildcard related) := by
    cases related with
    | LocalAccess => exact local_persists tree initial protections root query queryNode maximum area old depth included removed afterRemoved legalAfter subset classified
    | ForeignAccess => exact foreign_persists tree initial protections root query queryNode maximum area old depth included found removed afterRemoved legalAfter subset classified
  rcases operation with ⟨classified,same,sameMask⟩ | ⟨exact,recorded,next,delta,classified,record,actual,same,sameMask⟩
  · subst after
    subst afterRemoved
    refine ⟨materialized_origin tree initial current protections maximum origin index node present,?_⟩
    intro query queryNode included found
    rw [GeneralBorrowExposedVirtualSchedule.materialized_effective tree current index node present query queryNode found]
    exact safe query queryNode included found
  · subst after
    have raw := (relation_matches tree initial current protections .Write removed matching coherent short root index node maximum 0).symm.trans classified
    have oldPermission := GeneralBorrowEventTransitionMetadata.record_permission _ _ .Write exact record
    have good : Compatible next exact (protections.contains node.tag) := by
      cases exact with
      | LocalAccess => exact local_effects recorded next _ delta actual
      | ForeignAccess => exact (DuplicatePrefixVirtualWriteClosureState.foreign_effects recorded next _ delta actual).1
    have cutoff : CutoffOrigin tree initial (updated tree current index node protections recorded next delta) protections maximum := by
      apply updated_origin tree initial current protections maximum origin index node present recorded next delta
      · intro above supported
        cases exact with
        | LocalAccess =>
          have bound := DuplicatePrefixResidualWriteSkip.residual_dominates tree initial protections removed root index (old.covers index inside)
          have parts := DuplicatePrefixCrossKindQueryGuard.local_classification _ _ _ _ bound raw
          rw [parts.2.1] at above
          cases above
        | ForeignAccess =>
          have preserved := (DuplicatePrefixVirtualWriteClosureState.foreign_effects recorded next _ delta actual).2.2 supported
          exact preserved.trans oldPermission
      · intro above unsupported
        cases exact with
        | LocalAccess =>
          have bound := DuplicatePrefixResidualWriteSkip.residual_dominates tree initial protections removed root index (old.covers index inside)
          have parts := DuplicatePrefixCrossKindQueryGuard.local_classification _ _ _ _ bound raw
          rw [parts.2.1] at above
          cases above
        | ForeignAccess =>
          have noGain := (DuplicatePrefixVirtualWriteClosureState.foreign_effects recorded next _ delta actual).2.1
          apply noGain
          simpa only [support,oldPermission] using unsupported
    refine ⟨cutoff,?_⟩
    intro query queryNode included found
    by_cases same : query = index
    · subst query
      have nodeEq : queryNode = node := Option.some.inj (found.symm.trans present)
      subst queryNode
      right
      simp only [effective,updated,GeneralBorrowWildcardSubtreeState.write_same,Option.getD_some]
      exact ⟨exact,good,persist index node inside present exact raw⟩
    · simp only [effective,updated_other tree current index query node protections recorded next delta same]
      rcases safe query queryNode included found with unchanged | ⟨related,compatible,classified⟩
      · exact .inl unchanged
      · exact .inr ⟨related,compatible,persist query queryNode included found related classified⟩
end DuplicatePrefix.DuplicatePrefixPrimaryWriteClosureState
