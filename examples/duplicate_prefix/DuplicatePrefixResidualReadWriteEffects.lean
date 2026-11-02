import duplicate_prefix.DuplicatePrefixResidualReadWriteStep
namespace DuplicatePrefix.DuplicatePrefixResidualReadWriteEffects
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
open DuplicatePrefixResidualCountModel
open GeneralBorrowProtectedReadCompatible (Compatible)
open GeneralBorrowExposedConditionalWritePermissions (support)
open DuplicatePrefixResidualWriteStep (Lost removedAfter loss_fresh updated_matches)
open GeneralBorrowExposedNonleafState (updated updated_other)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Supporting permissions retain their initial origin; accessed/SIFA fields
are deliberately unrestricted. This is a state invariant, not a success claim. -/
def Origin (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags) : Prop :=
  ∀ index node, tree.nodes.get index = some node → node.isExposed = true →
    support ((current.perms.get index).getD node.defaultLocationState) (protections.contains node.tag) = true →
    ((current.perms.get index).getD node.defaultLocationState).permission =
      ((initial.perms.get index).getD node.defaultLocationState).permission

theorem origin_initial (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags) :
    Origin tree initial initial protections := by unfold Origin; intros; rfl

/-- Either visitation only materializes the effective state, so Origin is
unchanged even when the previously vacant physical slot becomes present. -/
theorem materialized_origin (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (origin : Origin tree initial current protections) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) :
    Origin tree initial (GeneralBorrowWildcardVirtualLeaf.materialized current index node) protections := by
  intro query queryNode found exposed supported
  have same := GeneralBorrowExposedVirtualSchedule.materialized_effective tree current index node present query queryNode found
  change support (GeneralBorrowWildcardVirtualLeaf.effective _ query queryNode) _ = true at supported
  change (GeneralBorrowWildcardVirtualLeaf.effective _ query queryNode).permission = _
  rw [same] at supported ⊢
  exact origin query queryNode found exposed supported

/-- Materialization also leaves the Write contribution model unchanged. -/
theorem materialized_matches (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (removed : List UniIndex) (matching : Matches tree initial current protections .Write removed)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node) :
    Matches tree initial (GeneralBorrowWildcardVirtualLeaf.materialized current index node) protections .Write removed := by
  intro query queryNode found exposed
  have same := GeneralBorrowExposedVirtualSchedule.materialized_effective tree current index node present query queryNode found
  change GeneralBorrowExposureCardinality.supports
    ((GeneralBorrowWildcardVirtualLeaf.effective _ query queryNode).permission.strongestAllowedLocalAccess _) .Write = _
  rw [same]
  exact matching query queryNode found exposed

/-- Scalar extraction from a real successful Read: if Write support remains,
the permission is unchanged. The public visit/step below derive success. -/
theorem successful_supporting_permission (state next : LocationState) (related : AccessRelatedness)
    (held : Bool) (delta : PermTransition) (initial : Compatible state related held)
    (actual : state.performAccess .Read related held = .Success next delta)
    (supported : support next held = true) : next.permission = state.permission := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases accessed <;> cases sifa <;> cases related <;> cases held <;>
      simp [Compatible,LocationState.possible,Permission.isUnique] at initial
    all_goals change LocationState.AccessResult.Success _ _ = .Success next delta at actual
    all_goals cases actual
    all_goals simp_all [support,GeneralBorrowExposureCardinality.supports,
      Permission.strongestAllowedLocalAccess,GeneralBorrowExposureAncestorFold.supportsWrite]
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases accessed <;> cases sifa <;> cases related <;> cases held <;>
      simp [Compatible,LocationState.possible,Permission.isUnique] at initial
    all_goals change LocationState.AccessResult.Success _ _ = .Success next delta at actual
    all_goals cases actual
    all_goals simp_all [support,GeneralBorrowExposureCardinality.supports,
      Permission.strongestAllowedLocalAccess,GeneralBorrowExposureAncestorFold.supportsWrite]

/-- Generic optional-state update frame preserves Origin when every surviving
Write support has its previous permission and no Write support is gained. -/
theorem updated_origin (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (origin : Origin tree initial current protections) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) (recorded next : LocationState) (delta : PermTransition)
    (noGain : support ((current.perms.get index).getD node.defaultLocationState) (protections.contains node.tag) = false →
      support next (protections.contains node.tag) = false)
    (preserved : support next (protections.contains node.tag) = true → next.permission =
      ((current.perms.get index).getD node.defaultLocationState).permission) :
    Origin tree initial (updated tree current index node protections recorded next delta) protections := by
  intro query queryNode found exposed supported
  by_cases same : query = index
  · subst query
    have nodeEq : queryNode = node := Option.some.inj (found.symm.trans present)
    subst queryNode
    simp only [updated,GeneralBorrowWildcardSubtreeState.write_same,Option.getD_some] at supported ⊢
    have oldSupported : support ((current.perms.get index).getD node.defaultLocationState) (protections.contains node.tag) = true := by
      cases old : support ((current.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)
      · rw [noGain old] at supported; cases supported
      · rfl
    exact (preserved supported).trans (origin index node present exposed oldSupported)
  · simp only [updated_other tree current index query node protections recorded next delta same] at supported ⊢
    exact origin query queryNode found exposed supported

/-- One actual scheduled Read advances the legal WRITE residual mask without
an untouched-slot premise. Only permissions of exposed surviving Write
supporters must retain their origin; SIFA/accessed may have changed earlier. -/
theorem step_origin (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (rootPosition : Nat)
    (removed : List UniIndex) (legal : Removal tree initial protections maximum .Write removed)
    (matching : Matches tree initial current protections .Write removed)
    (origin : Origin tree initial current protections)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree current protections)
    (short : tree.nodes.size < 65536) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (present : tree.nodes.get index = some node)
    (query : WildcardAccessRelatedness) (related : AccessRelatedness)
    (source : relation current root index node maximum .Read rootPosition = some query)
    (exactQuery : exactRelation query = some related)
    (compatible : Compatible ((current.perms.get index).getD node.defaultLocationState) related (protections.contains node.tag))
    (scheduled : GeneralBorrowEvents.Scheduled ((current.perms.get index).getD node.defaultLocationState) .Read related) :
    ∃ recorded next delta,
      ((current.perms.get index).getD node.defaultLocationState).recordNewAccess .Read related = .Recorded recorded ∧
      recorded.performAccess .Read related (protections.contains node.tag) = .Success next delta ∧
      Compatible next related (protections.contains node.tag) ∧
      Removal tree initial protections maximum .Write (removedAfter current protections removed index node next) ∧
      Matches tree initial (updated tree current index node protections recorded next delta) protections .Write
        (removedAfter current protections removed index node next) ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree (updated tree current index node protections recorded next delta) protections ∧
      (∀ query, query ≠ index → (updated tree current index node protections recorded next delta).perms.get query = current.perms.get query) ∧
      Origin tree initial (updated tree current index node protections recorded next delta) protections := by
  obtain ⟨recorded,next,delta,record,actual,good,noGain,lossPermission⟩ :=
    DuplicatePrefixResidualReadWriteSupport.visit _ related _ compatible scheduled
  have preserved : support next (protections.contains node.tag) = true → next.permission =
      ((current.perms.get index).getD node.defaultLocationState).permission := by
    have recordedEq : recorded = {((current.perms.get index).getD node.defaultLocationState) with idempotentForeignAccess :=
      (IdempotentForeignAccess.recordNew ((current.perms.get index).getD node.defaultLocationState).idempotentForeignAccess
        (IdempotentForeignAccess.fromAccessAndRelatedness .Read related))} := by
      simpa [LocationState.recordNewAccess,GeneralBorrowEvents.scheduled_recurse _ _ _ scheduled] using record.symm
    have recordedCompatible : Compatible recorded related (protections.contains node.tag) := by
      rw [recordedEq]
      exact compatible
    intro supported
    exact (successful_supporting_permission recorded next related _ delta recordedCompatible actual supported).trans
      (GeneralBorrowEventTransitionMetadata.record_permission _ _ .Read related record)
  refine ⟨recorded,next,delta,record,actual,good,?_,
    updated_matches tree initial current protections removed matching index node present recorded next delta noGain,
    GeneralBorrowExposedNonleafCoherence.updated_coherent tree current index node protections recorded next delta related
      depth present coherent record actual,
    (fun query different => updated_other tree current index query node protections recorded next delta different),
    updated_origin tree initial current protections origin index node present recorded next delta noGain preserved⟩
  by_cases loss : Lost current protections index node next
  · have fresh := loss_fresh tree initial current protections removed matching index node present next loss
    obtain ⟨foreign,permission⟩ := lossPermission loss.2.1 loss.2.2
    have queryForeign : query = .ForeignAccess := by cases query <;> simp_all [exactRelation]
    subst query
    have above := DuplicatePrefixResidualReadWriteSupport.source_read_foreign_above tree current protections root index node maximum rootPosition
      coherent short present loss.1 loss.2.1 source
    have permissionEq := origin index node present loss.1 loss.2.1
    have initialSupport : support ((initial.perms.get index).getD node.defaultLocationState) (protections.contains node.tag) = true := by
      simpa only [support,←permissionEq] using loss.2.1
    have initialPermission : losesWriteWhenForeign ((initial.perms.get index).getD node.defaultLocationState).permission = true := by
      rw [←permissionEq]; exact permission
    have initialAllowed : removable initial protections maximum .Write index node = true := by
      change node.isExposed && aboveMaximum node maximum &&
        support ((initial.perms.get index).getD node.defaultLocationState) (protections.contains node.tag) &&
        losesWriteWhenForeign ((initial.perms.get index).getD node.defaultLocationState).permission = true
      simp [loss.1,above,initialSupport,initialPermission]
    simpa only [removedAfter,if_pos loss] using
      removal_cons tree initial protections maximum .Write removed legal index fresh node present initialAllowed
  · simpa only [removedAfter,if_neg loss] using legal
end DuplicatePrefix.DuplicatePrefixResidualReadWriteEffects
