import duplicate_prefix.GeneralBorrowSnapshotReadDFS
import duplicate_prefix.GeneralBorrowSnapshotVirtualReadAccess
import duplicate_prefix.GeneralBorrowSnapshotPrimaryReadPlan
import duplicate_prefix.GeneralBorrowStructuralHistoryState
import duplicate_prefix.GeneralBorrowExposedScopedReciprocal
namespace DuplicatePrefix.GeneralBorrowReadNoMaximumWriteFrame
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

def WriteFrame (before after : LocationTree) : Prop := ∀ query, counter after.exposedCache query .Write = counter before.exposedCache query .Write

/-- No-cutoff Read effects cannot legally remove any Write contribution.
Coherent physical counters therefore remain equal globally. -/
theorem of_effects (tree : BorrowTree) (before after : LocationTree) (protections : ProtectedTags)
    (beforeCoherent : LocationCoherent tree before protections) (afterCoherent : LocationCoherent tree after protections)
    (effects : GeneralBorrowSnapshotReadWriteEffects.Effects tree before after protections none) : WriteFrame before after := by
  obtain ⟨removed,legal,matching,origin⟩ := effects
  have empty := DuplicatePrefixResidualSupportAuthorization.no_maximum_removal_empty tree before protections .Write removed legal
  subst removed
  intro query
  rw [afterCoherent query .Write,beforeCoherent query .Write]
  congr 1
  exact (DuplicatePrefixResidualCountModel.counts_match tree before after protections .Write [] matching query).trans
    (DuplicatePrefixResidualSupportAuthorization.residual_empty tree before protections .Write query)

/-- Actual virtual Read derives the no-cutoff global Write-counter frame from
raw S01 Read authorization, without an operation/frame premise. -/
theorem virtual (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (nonzero : position ≠ 0) (support : UniIndex → Prop)
    (authorization : DuplicatePrefixResidualSupportAuthorization.Authorization tree location protections root position none .Read support)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (coherent : LocationCoherent tree location protections) (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location) :
    WriteFrame location (tree.performWildcardAccessAt location root none .Read protections true).location := by
  obtain ⟨_,_,_,_,afterCoherent,_,_,_,_,effects⟩ :=
    GeneralBorrowSnapshotVirtualReadAccess.of_authorization_effects tree location protections root position none nonzero support authorization depth forest coherent short profile possible
  exact of_effects tree location _ protections coherent afterCoherent effects

/-- The primary no-cutoff Read derives the same global Write-counter frame. -/
theorem primary (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree) (root : UniIndex) (support : UniIndex → Prop)
    (authorization : DuplicatePrefixResidualSupportAuthorization.Authorization tree location protections root 0 none .Read support)
    (coherent : LocationCoherent tree location protections) (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location) :
    WriteFrame location (tree.performWildcardAccessAt location root none .Read protections false).location := by
  obtain ⟨forest⟩ := formed.forest location protections
  obtain ⟨depth⟩ := formed.depth
  have graph := GeneralBorrowExposedScopedReciprocal.of_forest tree location protections forest depth
  obtain ⟨plan⟩ := GeneralBorrowSnapshotPrimaryReadPlan.of_authorization tree location protections root support depth graph coherent short authorization
  let weights := GeneralBorrowWildcardForestWeights.of_forest tree location protections forest
  let control := GeneralBorrowWildcardControlStack.Support.of_authorization tree location protections root 0 none .Read support authorization
  have snapshot := DuplicatePrefixResidualInitialSnapshot.snapshot tree location protections root 0 none .Read support authorization coherent short
  obtain ⟨_,_,_,_,afterCoherent,_,_,_,_,effects,_⟩ := GeneralBorrowSnapshotReadDFS.access_plan_transfer tree location protections root 0 none
    weights (GeneralBorrowWildcardForestWeights.bounded tree location protections forest root) control snapshot depth coherent plan profile possible short
  exact of_effects tree location _ protections coherent afterCoherent effects

end DuplicatePrefix.GeneralBorrowReadNoMaximumWriteFrame
