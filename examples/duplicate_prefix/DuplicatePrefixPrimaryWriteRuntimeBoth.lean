import duplicate_prefix.DuplicatePrefixPrimaryWriteBothClosure
import duplicate_prefix.GeneralBorrowResidualSavedWriteRuntime
namespace DuplicatePrefix.DuplicatePrefixPrimaryWriteRuntimeBoth
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization DuplicatePrefixResidualCountModel
open GeneralBorrowWildcardControlWitness
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- The same deterministic primary no-maximum Write result has both derived
successor callback candidates and all runtime row invariants. Runtime and
candidate proofs are joined at the actual source result; neither a successor
capability nor an operation-success premise is accepted. -/
theorem access (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (root : UniIndex) (support : UniIndex → Prop)
    (authorization : Authorization tree initial protections root 0 none .Write support)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let result := tree.performWildcardAccessAt initial root none .Write protections false
    result.status = .Completed ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
      (∀ query, tree.nodes.get query = none → result.location.perms.get query = initial.perms.get query) ∧
      Matches tree initial result.location protections .Write [] ∧
      Snapshot tree result.location protections root 0 none .Write support ∧
      Snapshot tree result.location protections root 0 none .Read support ∧
      Authorization tree result.location protections root 0 none .Write support ∧
      Authorization tree result.location protections root 0 none .Read support ∧
      (∀ query, ¬support query → result.location.perms.get query = initial.perms.get query) := by
  obtain ⟨done,afterCoherent,matching,writeSnapshot,readSnapshot,writeAfter,readAfter,outside⟩ :=
    DuplicatePrefixPrimaryWriteBothClosure.access tree initial protections formed root support authorization coherent short
  obtain ⟨forest⟩ := formed.forest initial protections
  obtain ⟨depth⟩ := formed.depth
  have graph := GeneralBorrowExposedScopedReciprocal.of_forest tree initial protections forest depth
  obtain ⟨witness,node,included,present,eligible⟩ := authorization.witness rfl
  have path := path_of_covers tree depth root witness node present (authorization.covers witness included)
  let plan := DuplicatePrefixResidualWriteWitnessPlan.primary tree initial protections root witness node present eligible path depth graph short
  let weights := GeneralBorrowWildcardForestWeights.of_forest tree initial protections forest
  let area := GeneralBorrowWildcardControlStack.Support.of_authorization tree initial protections root 0 none .Write support authorization
  have runtime := GeneralBorrowResidualSavedWriteRuntime.access tree initial protections root 0 none weights
    (GeneralBorrowWildcardForestWeights.bounded tree initial protections forest root) area plan authorization depth forest coherent short profile possible
  have physicalEq : ((0 : Nat) != 0) = false := rfl
  simp only [physicalEq] at runtime
  obtain ⟨_,removed,_,_,_,_,afterProfile,afterPossible,vacant⟩ := runtime
  exact ⟨done,afterCoherent,afterProfile,afterPossible,vacant,matching,writeSnapshot,readSnapshot,writeAfter,readAfter,outside⟩
end DuplicatePrefix.DuplicatePrefixPrimaryWriteRuntimeBoth
