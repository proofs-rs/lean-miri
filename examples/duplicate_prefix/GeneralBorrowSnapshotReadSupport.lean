import duplicate_prefix.GeneralBorrowSnapshotReadState
import duplicate_prefix.GeneralBorrowWildcardPrimaryReadWitness
namespace DuplicatePrefix.GeneralBorrowSnapshotReadSupport
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization
open GeneralBorrowWildcardVirtualLeaf (effective materialized)
open GeneralBorrowExposedNonleafState (ReadFrame updated updated_other)
open GeneralBorrowSnapshotReadState (wildcard)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem allows_read (level : WildcardAccessLevel) :
    GeneralBorrowExposureCardinality.supports level .Read = level.allows .Read := by cases level <;> rfl

/-- Actual successful Read endpoints retain Read support, even if Write
support changes. This extraction lemma is used only after the raw snapshot
has derived the real record/access equations. -/
theorem read_support_success (state recorded next : LocationState) (delta : PermTransition)
    (exact : AccessRelatedness) (held : Bool) (possible : state.possible = true)
    (record : state.recordNewAccess .Read exact = .Recorded recorded)
    (access : recorded.performAccess .Read exact held = .Success next delta) :
    (next.permission.strongestAllowedLocalAccess held).allows .Read =
      (state.permission.strongestAllowedLocalAccess held).allows .Read := by
  have permission := GeneralBorrowEventTransitionMetadata.record_permission state recorded .Read exact record
  have accessed : recorded.accessed = state.accessed := by
    unfold LocationState.recordNewAccess at record
    split at record
    · cases record; rfl
    · cases record
  have recordedPossible : recorded.possible = true := by
    simp only [LocationState.possible,permission,accessed]
    exact possible
  have compatible := (DuplicatePrefixScalarAuthorization.compatible_iff recorded .Read exact held recordedPossible).mpr ⟨next,delta,access⟩
  obtain ⟨actual,transition,performed,_,support⟩ := GeneralBorrowExposedConditionalReadPermissions.transition recorded exact held compatible
  have same : actual = next := (LocationState.AccessResult.Success.inj (performed.symm.trans access)).1
  rw [same] at support
  rw [←allows_read,←allows_read, support,permission]

/-- The raw postorder Read step additionally preserves the designated support
of EVERY present node. Counter-only ReadFrame does not imply this property;
it follows from the actual scalar transitions/materialization. The existing
post API remains unchanged, and no successful-operation premise is added. -/
theorem post_with_support (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) (support : UniIndex → Prop)
    (snapshot : Snapshot tree location protections root rootPosition maximum .Read support)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
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
      GeneralBorrowWildcardPrimaryReadWitness.PointwiseReadFrame tree protections location after := by
  obtain ⟨after,operations,afterSnapshot,frame,coherentAfter,other⟩ :=
    GeneralBorrowSnapshotReadState.post tree location protections root rootPosition maximum support snapshot depth coherent index node included present recurse
  refine ⟨after,operations,afterSnapshot,frame,coherentAfter,other,?_⟩
  rcases operations with ⟨_,materializedEq⟩ | ⟨exact,recorded,next,delta,classified,record,access,updatedEq⟩
  · subst after
    intro query queryNode found
    change ((effective (materialized location index node) query queryNode).permission.strongestAllowedLocalAccess _).allows .Read = _
    rw [GeneralBorrowExposedVirtualSchedule.materialized_effective tree location index node present query queryNode found]
    rfl
  · subst after
    have possible : (effective location index node).possible = true := by
      have authorized := snapshot.scalar index node included present
      rw [classified] at authorized
      cases exact <;> exact authorized.1
    have supportSame := read_support_success (effective location index node) recorded next delta exact
      (protections.contains node.tag) possible record access
    intro query queryNode found
    change ((effective (updated tree location index node protections recorded next delta) query queryNode).permission.strongestAllowedLocalAccess _).allows .Read = _
    by_cases same : query = index
    · subst query
      have nodeEq := Option.some.inj (present.symm.trans found)
      subst queryNode
      simpa only [updated,effective,GeneralBorrowExposureCardinality.effective,GeneralBorrowWildcardSubtreeState.write_same,Option.getD_some] using supportSame
    · simp only [effective,GeneralBorrowExposureCardinality.effective,updated_other tree location index query node protections recorded next delta same]

end DuplicatePrefix.GeneralBorrowSnapshotReadSupport
