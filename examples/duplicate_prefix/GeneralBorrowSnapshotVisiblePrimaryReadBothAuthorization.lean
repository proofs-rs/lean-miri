import duplicate_prefix.DuplicatePrefixReadWriteAnyPositionRebuild
import duplicate_prefix.GeneralBorrowSnapshotVisiblePrimaryReadPlan
import duplicate_prefix.GeneralBorrowSnapshotReadDFS
import duplicate_prefix.DuplicatePrefixResidualInitialSnapshot
import duplicate_prefix.GeneralBorrowStructuralHistoryState
import duplicate_prefix.GeneralBorrowExposedScopedReciprocal
namespace DuplicatePrefix.GeneralBorrowSnapshotVisiblePrimaryReadBothAuthorization
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
open GeneralBorrowExposedNonleafState (ReadFrame)
open GeneralBorrowWildcardPrimaryReadWitness (PointwiseReadFrame)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Actual primary callback under static visibility of one eligible witness.
No global parent-tag order or successful operation is assumed. -/
theorem access (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (root : UniIndex) (maximum : Option BorTag)
     (support : UniIndex → Prop)
    (read : Authorization tree initial protections root 0 maximum .Read support)
    (write : Authorization tree initial protections root 0 maximum .Write support)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (witness : UniIndex) (witnessNode : TreeNode)
    (witnessPresent : tree.nodes.get witness = some witnessNode)
    (witnessPath : GeneralBorrowExposedNonleafPrimaryPath.Path tree root witness)
    (visible : GeneralBorrowPrimaryWitnessVisibility.Visible tree maximum witness)
    (eligible : Supports initial protections witness witnessNode maximum .Read)
    (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let result := tree.performWildcardAccessAt initial root maximum .Read protections false
    result.status = .Completed ∧ ReadFrame initial result.location ∧
    Snapshot tree result.location protections root 0 maximum .Read support ∧
    PointwiseReadFrame tree protections initial result.location ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    (∀ query, ¬support query → result.location.perms.get query = initial.perms.get query) ∧
    GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
    (∀ query, tree.nodes.get query = none → result.location.perms.get query = initial.perms.get query) ∧
    Authorization tree result.location protections root 0 maximum .Read support ∧
    Authorization tree result.location protections root 0 maximum .Write support := by
  obtain ⟨forest⟩ := formed.forest initial protections
  obtain ⟨depth⟩ := formed.depth
  let weights := GeneralBorrowWildcardForestWeights.of_forest tree initial protections forest
  let control := GeneralBorrowWildcardControlStack.Support.of_authorization tree initial protections root 0 maximum .Read support read
  have initialSnapshot := DuplicatePrefixResidualInitialSnapshot.snapshot tree initial protections root 0 maximum .Read support read coherent short
  have graph := GeneralBorrowExposedScopedReciprocal.of_forest tree initial protections forest depth
  let plan := GeneralBorrowSnapshotVisiblePrimaryReadPlan.primary tree initial protections root maximum depth graph coherent short witness witnessNode witnessPresent visible eligible witnessPath
  obtain ⟨complete,frame,snapshot,pointwise,afterCoherent,outside,afterProfile,afterPossible,vacant,effects,transfer⟩ :=
    GeneralBorrowSnapshotReadDFS.access_plan_transfer tree initial protections root 0 maximum weights
      (GeneralBorrowWildcardForestWeights.bounded tree initial protections forest root) control initialSnapshot depth coherent plan profile possible short
  obtain ⟨removed,legal,matching,origin⟩ := effects
  have writeAfter := DuplicatePrefixReadWriteAnyPositionRebuild.rebuild tree initial _ protections root 0 maximum support read write coherent short removed legal matching origin afterPossible transfer
  have readAfter := DuplicatePrefixResidualSupportSnapshotBridge.of_snapshot tree _ protections root 0 maximum .Read support
    snapshot read.rooted read.present read.children read.covers afterCoherent short
    (fun removed legal => read_removal_empty tree _ protections maximum removed legal)
  exact ⟨complete,frame,snapshot,pointwise,afterCoherent,outside,afterProfile,afterPossible,vacant,readAfter,writeAfter⟩
/-- Same callback guarantee with one static cutoff-closed topology condition;
no additional witness packet is required from callers. -/
theorem access_closed (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (root : UniIndex) (maximum : Option BorTag)
    (closed : GeneralBorrowPrimaryWitnessVisibility.CutoffClosed tree maximum) (support : UniIndex → Prop)
    (read : Authorization tree initial protections root 0 maximum .Read support)
    (write : Authorization tree initial protections root 0 maximum .Write support)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let result := tree.performWildcardAccessAt initial root maximum .Read protections false
    result.status = .Completed ∧ ReadFrame initial result.location ∧
    Snapshot tree result.location protections root 0 maximum .Read support ∧
    PointwiseReadFrame tree protections initial result.location ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    (∀ query, ¬support query → result.location.perms.get query = initial.perms.get query) ∧
    GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
    (∀ query, tree.nodes.get query = none → result.location.perms.get query = initial.perms.get query) ∧
    Authorization tree result.location protections root 0 maximum .Read support ∧
    Authorization tree result.location protections root 0 maximum .Write support := by
  obtain ⟨depth⟩ := formed.depth
  obtain ⟨witness,node,included,present,eligible⟩ := read.witness rfl
  have path := GeneralBorrowWildcardControlWitness.path_of_covers tree depth root witness node present (read.covers witness included)
  have visible := GeneralBorrowPrimaryWitnessVisibility.visible_of_closed tree maximum closed initial protections .Read witness node present eligible
  exact access tree initial protections formed root maximum support read write coherent witness node present path visible eligible short profile possible

end DuplicatePrefix.GeneralBorrowSnapshotVisiblePrimaryReadBothAuthorization
