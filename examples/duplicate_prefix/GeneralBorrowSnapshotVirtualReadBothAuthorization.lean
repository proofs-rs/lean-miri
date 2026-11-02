import duplicate_prefix.GeneralBorrowSnapshotVirtualReadWriteAuthorization
import duplicate_prefix.DuplicatePrefixResidualSupportSnapshotBridge
import duplicate_prefix.GeneralBorrowSnapshotVirtualReadAccess
namespace DuplicatePrefix.GeneralBorrowSnapshotVirtualReadBothAuthorization
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
open GeneralBorrowExposedNonleafState (ReadFrame)
open GeneralBorrowWildcardPrimaryReadWitness (PointwiseReadFrame)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Raw Read and Write callback candidates supply a real virtual Read visitor
which retains the full Write candidate for its resulting state. All masks,
scalar transfer tables and actual visitor operations are derived internally.
This concerns one callback, not duplicate_prefix's complete execution. -/
theorem access_both (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) (support : UniIndex → Prop)
    (virtual : rootPosition ≠ 0)
    (read : Authorization tree initial protections root rootPosition maximum .Read support)
    (write : Authorization tree initial protections root rootPosition maximum .Write support)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree initial protections).topology)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let result := tree.performWildcardAccessAt initial root maximum .Read protections true
    result.status = .Completed ∧ ReadFrame initial result.location ∧
    Snapshot tree result.location protections root rootPosition maximum .Read support ∧
    PointwiseReadFrame tree protections initial result.location ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    (∀ query, ¬support query → result.location.perms.get query = initial.perms.get query) ∧
    GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
    (∀ query, tree.nodes.get query = none → result.location.perms.get query = initial.perms.get query) ∧
    Authorization tree result.location protections root rootPosition maximum .Read support ∧
    Authorization tree result.location protections root rootPosition maximum .Write support := by
  obtain ⟨complete,frame,snapshot,pointwise,afterCoherent,outside,afterProfile,afterPossible,vacant,writeAfter⟩ :=
    GeneralBorrowSnapshotVirtualReadWriteAuthorization.access tree initial protections root rootPosition maximum support virtual read write depth forest coherent short profile possible
  have readAfter := DuplicatePrefixResidualSupportSnapshotBridge.of_snapshot tree _ protections root rootPosition maximum .Read support
    snapshot read.rooted read.present read.children read.covers afterCoherent short
    (fun removed legal => read_removal_empty tree _ protections maximum removed legal)
  exact ⟨complete,frame,snapshot,pointwise,afterCoherent,outside,afterProfile,afterPossible,vacant,readAfter,writeAfter⟩
end DuplicatePrefix.GeneralBorrowSnapshotVirtualReadBothAuthorization
