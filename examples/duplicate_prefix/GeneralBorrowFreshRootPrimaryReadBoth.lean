import duplicate_prefix.GeneralBorrowSnapshotOrderedPrimaryReadBothAuthorization
import duplicate_prefix.GeneralBorrowFreshRootSupportReadPlan
namespace DuplicatePrefix.GeneralBorrowFreshRootPrimaryReadBoth
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
open GeneralBorrowExposedNonleafState (ReadFrame)
open GeneralBorrowWildcardPrimaryReadWitness (PointwiseReadFrame)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- Actual primary Read and BOTH callback/runtime successors under a fresh
cutoff. Only exposed contributors and the actual old-root support are bounded;
newer hidden nodes in other components remain arbitrary. The real DFS witness
plan is derived internally, without ParentTagOrder or successful-operation premises. -/
theorem access (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (root : UniIndex) (maximum : BorTag) (support : UniIndex → Prop)
    (exposed : GeneralBorrowFreshRootSupportCutoff.ExposedBound tree maximum)
    (bounded : GeneralBorrowFreshRootSupportCutoff.SupportBound tree maximum support)
    (read : Authorization tree initial protections root 0 (some maximum) .Read support)
    (write : Authorization tree initial protections root 0 (some maximum) .Write support)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let result := tree.performWildcardAccessAt initial root (some maximum) .Read protections false
    result.status = .Completed ∧ ReadFrame initial result.location ∧
    Snapshot tree result.location protections root 0 (some maximum) .Read support ∧
    PointwiseReadFrame tree protections initial result.location ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    (∀ query, ¬support query → result.location.perms.get query = initial.perms.get query) ∧
    GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
    (∀ query, tree.nodes.get query = none → result.location.perms.get query = initial.perms.get query) ∧
    Authorization tree result.location protections root 0 (some maximum) .Read support ∧
    Authorization tree result.location protections root 0 (some maximum) .Write support := by
  obtain ⟨forest⟩ := formed.forest initial protections
  obtain ⟨depth⟩ := formed.depth
  let weights := GeneralBorrowWildcardForestWeights.of_forest tree initial protections forest
  let control := GeneralBorrowWildcardControlStack.Support.of_authorization tree initial protections root 0 (some maximum) .Read support read
  have initialSnapshot := DuplicatePrefixResidualInitialSnapshot.snapshot tree initial protections root 0 (some maximum) .Read support read coherent short
  have graph := GeneralBorrowExposedScopedReciprocal.of_forest tree initial protections forest depth
  obtain ⟨plan⟩ := GeneralBorrowFreshRootSupportReadPlan.of_authorization tree initial protections root maximum support exposed bounded depth graph coherent short read
  obtain ⟨complete,frame,snapshot,pointwise,afterCoherent,outside,afterProfile,afterPossible,vacant,effects,transfer⟩ :=
    GeneralBorrowSnapshotReadDFS.access_plan_transfer tree initial protections root 0 (some maximum) weights
      (GeneralBorrowWildcardForestWeights.bounded tree initial protections forest root) control initialSnapshot depth coherent plan profile possible short
  obtain ⟨removed,legal,matching,origin⟩ := effects
  have writeAfter := DuplicatePrefixReadWriteAnyPositionRebuild.rebuild tree initial _ protections root 0 (some maximum) support read write coherent short removed legal matching origin afterPossible transfer
  have readAfter := DuplicatePrefixResidualSupportSnapshotBridge.of_snapshot tree _ protections root 0 (some maximum) .Read support
    snapshot read.rooted read.present read.children read.covers afterCoherent short
    (fun removed legal => read_removal_empty tree _ protections maximum removed legal)
  exact ⟨complete,frame,snapshot,pointwise,afterCoherent,outside,afterProfile,afterPossible,vacant,readAfter,writeAfter⟩
end DuplicatePrefix.GeneralBorrowFreshRootPrimaryReadBoth
