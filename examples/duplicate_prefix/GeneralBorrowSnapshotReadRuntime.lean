import duplicate_prefix.GeneralBorrowSnapshotReadSupport
import duplicate_prefix.GeneralBorrowLocationSifaConsistency
namespace DuplicatePrefix.GeneralBorrowSnapshotReadRuntime
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization
open GeneralBorrowWildcardVirtualLeaf (effective materialized)
open GeneralBorrowExposedNonleafState (ReadFrame updated updated_other)
open GeneralBorrowSnapshotReadState (wildcard)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- All physically present nodes have possible scalar states, irrespective of
which component the current callback traverses. -/
def GlobalPossible (tree : BorrowTree) (location : LocationTree) : Prop :=
  ∀ query queryNode, tree.nodeAt query = some queryNode → (effective location query queryNode).possible = true

theorem vacant_frame (tree : BorrowTree) (before after : LocationTree) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node)
    (other : ∀ query, query ≠ index → after.perms.get query = before.perms.get query) :
    ∀ query, tree.nodes.get query = none → after.perms.get query = before.perms.get query := by
  intro query missing
  apply other query
  intro same
  subst query
  rw [present] at missing
  cases missing

theorem materialized_profile (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location protections) :
    GeneralBorrowLocationSifaConsistency.Profile tree (materialized location index node) protections := by
  refine ⟨?_,?_⟩
  · intro query queryNode found
    change GeneralBorrowSifaPermissionConsistency.Consistent (effective (materialized location index node) query queryNode) _
    rw [GeneralBorrowExposedVirtualSchedule.materialized_effective tree location index node present query queryNode found]
    exact profile.present query queryNode found
  · intro query missing
    have different : query ≠ index := by intro same; subst query; rw [present] at missing; cases missing
    have other : (materialized location index node).perms.get query = location.perms.get query := by
      unfold materialized UniValMap.orInsert
      split
      · rfl
      · exact GeneralBorrowFreshLocation.get_other _ index query _ different
    rw [other]
    exact profile.vacant query missing

/-- The actual recorded scalar pipeline preserves physical permission/SIFA
consistency at the changed node; literal storage framing handles every other
present node and every vacancy. This extraction lemma is used only after the
raw snapshot derives its real record/access results. -/
theorem updated_profile (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
    (recorded next : LocationState) (delta : PermTransition) (kind : AccessKind) (exact : AccessRelatedness)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location protections)
    (record : (effective location index node).recordNewAccess kind exact = .Recorded recorded)
    (access : recorded.performAccess kind exact (protections.contains node.tag) = .Success next delta) :
    GeneralBorrowLocationSifaConsistency.Profile tree (updated tree location index node protections recorded next delta) protections := by
  have nextConsistent := GeneralBorrowSifaPermissionConsistency.pipeline (effective location index node) recorded next delta kind exact
    (protections.contains node.tag) (profile.present index node present) record access
  refine ⟨?_,?_⟩
  · intro query queryNode found
    by_cases same : query = index
    · subst query
      have nodeEq : queryNode = node := Option.some.inj (found.symm.trans present)
      subst queryNode
      simpa only [updated,GeneralBorrowWildcardSubtreeState.write_same,Option.getD_some] using nextConsistent
    · simpa only [updated_other tree location index query node protections recorded next delta same] using profile.present query queryNode found
  · intro query missing
    rw [vacant_frame tree location _ index node present
      (fun query different => updated_other tree location index query node protections recorded next delta different) query missing]
    exact profile.vacant query missing

private theorem scalar_possible (state : LocationState) (held : Bool) (query : Option WildcardAccessRelatedness)
    (scalar : Scalar state .Read held query) : state.possible = true := by
  cases query with
  | none => exact False.elim scalar
  | some related => cases related <;> first | exact scalar.1 | exact scalar

/-- The full real postorder Read node action preserves runtime invariants,
including physical SIFA consistency and clean vacancies, not just the raw
snapshot/cache/support model. All operations are derived by the frozen raw
post theorem. No ownership, leaf shape or successful-operation input is used. -/
theorem post_with_runtime (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) (support : UniIndex → Prop)
    (snapshot : Snapshot tree location protections root rootPosition maximum .Read support)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location protections)
    (possible : GlobalPossible tree location)
    (index : UniIndex) (node : TreeNode) (included : support index) (present : tree.nodes.get index = some node)
    (recurse : DuplicatePrefixCallbackVisitAuthorization.entrySkip (effective location index node) .Read
      (relation location root index node maximum .Read rootPosition) = false) :
    ∃ after,
      ((relation location root index node maximum .Read rootPosition = some .EitherAccess ∧ after = materialized location index node) ∨
       ∃ exact recorded next delta,
         relation location root index node maximum .Read rootPosition = some (wildcard exact) ∧
         (effective location index node).recordNewAccess .Read exact = .Recorded recorded ∧
         recorded.performAccess .Read exact (protections.contains node.tag) = .Success next delta ∧
         after = updated tree location index node protections recorded next delta) ∧
      Snapshot tree after protections root rootPosition maximum .Read support ∧
      ReadFrame location after ∧ GeneralBorrowExposureCardinality.LocationCoherent tree after protections ∧
      (∀ query, query ≠ index → after.perms.get query = location.perms.get query) ∧
      GeneralBorrowWildcardPrimaryReadWitness.PointwiseReadFrame tree protections location after ∧
      GeneralBorrowLocationSifaConsistency.Profile tree after protections ∧
      (∀ query, tree.nodes.get query = none → after.perms.get query = location.perms.get query) ∧
      GlobalPossible tree after := by
  obtain ⟨after,action,afterSnapshot,frame,afterCoherent,other,pointwise⟩ :=
    GeneralBorrowSnapshotReadSupport.post_with_support tree location protections root rootPosition maximum support
      snapshot depth coherent index node included present recurse
  refine ⟨after,action,afterSnapshot,frame,afterCoherent,other,pointwise,?_,
    vacant_frame tree location after index node present other,?_⟩
  · rcases action with ⟨_,same⟩ | ⟨exact,recorded,next,delta,_,record,access,same⟩
    · subst after
      exact materialized_profile tree location protections index node present profile
    · subst after
      exact updated_profile tree location protections index node present recorded next delta .Read exact profile record access
  · intro query queryNode found
    by_cases same : query = index
    · subst query
      have nodeEq : queryNode = node := Option.some.inj (found.symm.trans present)
      subst queryNode
      exact scalar_possible _ _ _ (afterSnapshot.scalar index node included present)
    · simpa only [effective,other query same] using possible query queryNode found
end DuplicatePrefix.GeneralBorrowSnapshotReadRuntime
