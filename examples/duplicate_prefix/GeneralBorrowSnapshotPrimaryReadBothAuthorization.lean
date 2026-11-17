import duplicate_prefix.DuplicatePrefixReadWriteNoMaximumRebuild
import duplicate_prefix.GeneralBorrowSnapshotPrimaryReadPlan
import duplicate_prefix.GeneralBorrowSnapshotReadDFS
import duplicate_prefix.DuplicatePrefixResidualInitialSnapshot
import duplicate_prefix.GeneralBorrowStructuralHistoryState
import duplicate_prefix.GeneralBorrowExposedScopedReciprocal
namespace DuplicatePrefix.GeneralBorrowSnapshotPrimaryReadBothAuthorization
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
open GeneralBorrowExposedNonleafState (ReadFrame)
open GeneralBorrowWildcardPrimaryReadWitness (PointwiseReadFrame)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Raw Read/Write callback candidates at a physical root with no tag maximum
supply the actual Read visitor and preserve BOTH candidates. The path witness,
Write mask and scalar transfer table are internally derived. -/
theorem access (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (root : UniIndex) (support : UniIndex → Prop)
    (read : Authorization tree initial protections root 0 none .Read support)
    (write : Authorization tree initial protections root 0 none .Write support)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let result := tree.performWildcardAccessAt initial root none .Read protections false
    result.status = .Completed ∧ ReadFrame initial result.location ∧
    Snapshot tree result.location protections root 0 none .Read support ∧
    PointwiseReadFrame tree protections initial result.location ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    (∀ query, ¬support query → result.location.perms.get query = initial.perms.get query) ∧
    GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
    (∀ query, tree.nodes.get query = none → result.location.perms.get query = initial.perms.get query) ∧
    Authorization tree result.location protections root 0 none .Read support ∧
    Authorization tree result.location protections root 0 none .Write support := by
  obtain ⟨forest⟩ := formed.forest initial protections
  obtain ⟨depth⟩ := formed.depth
  let weights := GeneralBorrowWildcardForestWeights.of_forest tree initial protections forest
  let control := GeneralBorrowWildcardControlStack.Support.of_authorization tree initial protections root 0 none .Read support read
  have initialSnapshot := DuplicatePrefixResidualInitialSnapshot.snapshot tree initial protections root 0 none .Read support read coherent short
  have graph := GeneralBorrowExposedScopedReciprocal.of_forest tree initial protections forest depth
  obtain ⟨plan⟩ := GeneralBorrowSnapshotPrimaryReadPlan.of_authorization tree initial protections root support depth graph coherent short read
  obtain ⟨complete,frame,snapshot,pointwise,afterCoherent,outside,afterProfile,afterPossible,vacant,effects,transfer⟩ :=
    GeneralBorrowSnapshotReadDFS.access_plan_transfer tree initial protections root 0 none weights
      (GeneralBorrowWildcardForestWeights.bounded tree initial protections forest root) control initialSnapshot depth coherent plan profile possible short
  obtain ⟨removed,legal,matching,origin⟩ := effects
  have writeAfter := DuplicatePrefixReadWriteNoMaximumRebuild.rebuild tree initial _ protections root 0 support write coherent short removed legal matching afterPossible transfer
  have readAfter := DuplicatePrefixResidualSupportSnapshotBridge.of_snapshot tree _ protections root 0 none .Read support
    snapshot read.rooted read.present read.children read.covers afterCoherent short
    (fun removed legal => read_removal_empty tree _ protections none removed legal)
  exact ⟨complete,frame,snapshot,pointwise,afterCoherent,outside,afterProfile,afterPossible,vacant,readAfter,writeAfter⟩
end DuplicatePrefix.GeneralBorrowSnapshotPrimaryReadBothAuthorization
