import duplicate_prefix.GeneralBorrowSnapshotPrimaryReadPlan
import duplicate_prefix.GeneralBorrowSnapshotReadDFS
import duplicate_prefix.DuplicatePrefixResidualInitialSnapshot
import duplicate_prefix.GeneralBorrowStructuralHistoryState
import duplicate_prefix.GeneralBorrowExposedScopedReciprocal
namespace DuplicatePrefix.GeneralBorrowSnapshotPrimaryReadAccess
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection DuplicatePrefixCallbackAuthorization
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Actual physical-root Read with no maximum-tag filter, from raw S01
callback authorization and graph/cache resources. The supporting witness is
reached by the real DFS; neither a witness plan nor operation success is a
caller premise. This is one callback, not the complete function invocation. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (root : UniIndex) (support : UniIndex → Prop)
    (authorization : DuplicatePrefixResidualSupportAuthorization.Authorization tree location protections root 0 none .Read support)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536) :
    let result := tree.performWildcardAccessAt location root none .Read protections false
    result.status = .Completed ∧ GeneralBorrowExposedNonleafState.ReadFrame location result.location ∧
    Snapshot tree result.location protections root 0 none .Read support ∧
    GeneralBorrowWildcardPrimaryReadWitness.PointwiseReadFrame tree protections location result.location ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections := by
  obtain ⟨forest⟩ := formed.forest location protections
  obtain ⟨depth⟩ := formed.depth
  let weights := GeneralBorrowWildcardForestWeights.of_forest tree location protections forest
  let control := GeneralBorrowWildcardControlStack.Support.of_authorization tree location protections root 0 none .Read support authorization
  have snapshot := DuplicatePrefixResidualInitialSnapshot.snapshot tree location protections root 0 none .Read support authorization coherent short
  have graph := GeneralBorrowExposedScopedReciprocal.of_forest tree location protections forest depth
  obtain ⟨plan⟩ := GeneralBorrowSnapshotPrimaryReadPlan.of_authorization tree location protections root support depth graph coherent short authorization
  exact GeneralBorrowSnapshotReadDFS.access_plan tree location protections root 0 none weights
    (GeneralBorrowWildcardForestWeights.bounded tree location protections forest root) control snapshot depth coherent plan

end DuplicatePrefix.GeneralBorrowSnapshotPrimaryReadAccess
