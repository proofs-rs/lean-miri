import duplicate_prefix.GeneralBorrowSnapshotOrderedPrimaryReadPlan
import duplicate_prefix.GeneralBorrowSnapshotReadDFS
import duplicate_prefix.DuplicatePrefixResidualInitialSnapshot
import duplicate_prefix.GeneralBorrowStructuralHistoryState
import duplicate_prefix.GeneralBorrowExposedScopedReciprocal
namespace DuplicatePrefix.GeneralBorrowSnapshotOrderedPrimaryReadRuntime
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection DuplicatePrefixCallbackAuthorization
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Actual physical-root Read with an arbitrary cutoff and an explicit
independent ParentTagOrder condition, from raw S01
callback authorization and graph/cache resources. The supporting witness is
reached by the real DFS; neither a witness plan nor operation success is a
caller premise. ParentTagOrder is not derived from RuntimeFacts or S01;
valid-input coverage is unproved. This is one callback, not the function invocation. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (root : UniIndex) (maximum : Option BorTag)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree) (support : UniIndex → Prop)
    (authorization : DuplicatePrefixResidualSupportAuthorization.Authorization tree location protections root 0 maximum .Read support)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location) :
    let result := tree.performWildcardAccessAt location root maximum .Read protections false
    result.status = .Completed ∧ GeneralBorrowExposedNonleafState.ReadFrame location result.location ∧
    Snapshot tree result.location protections root 0 maximum .Read support ∧
    GeneralBorrowWildcardPrimaryReadWitness.PointwiseReadFrame tree protections location result.location ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    (∀ query, ¬support query → result.location.perms.get query = location.perms.get query) ∧
    GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
    (∀ query, tree.nodes.get query = none → result.location.perms.get query = location.perms.get query) := by
  obtain ⟨forest⟩ := formed.forest location protections
  obtain ⟨depth⟩ := formed.depth
  let weights := GeneralBorrowWildcardForestWeights.of_forest tree location protections forest
  let control := GeneralBorrowWildcardControlStack.Support.of_authorization tree location protections root 0 maximum .Read support authorization
  have snapshot := DuplicatePrefixResidualInitialSnapshot.snapshot tree location protections root 0 maximum .Read support authorization coherent short
  have graph := GeneralBorrowExposedScopedReciprocal.of_forest tree location protections forest depth
  obtain ⟨plan⟩ := GeneralBorrowSnapshotOrderedPrimaryReadPlan.of_authorization tree location protections root maximum support order depth graph coherent short authorization
  exact GeneralBorrowSnapshotReadDFS.access_plan_runtime tree location protections root 0 maximum weights
    (GeneralBorrowWildcardForestWeights.bounded tree location protections forest root) control snapshot depth coherent plan profile possible

end DuplicatePrefix.GeneralBorrowSnapshotOrderedPrimaryReadRuntime
