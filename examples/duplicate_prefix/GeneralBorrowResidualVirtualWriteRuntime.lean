import duplicate_prefix.GeneralBorrowResidualSavedWriteRuntime

namespace DuplicatePrefix.GeneralBorrowResidualVirtualWriteRuntime
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixResidualSupportAuthorization DuplicatePrefixResidualCountModel
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- Full real virtual-root Write DFS with runtime preservation from raw S01
authorization and initial runtime facts. Weights, traversal support and the
virtual witness plan are derived; no extra leaf, ownership, tag-order, root
geometry, free-pool or successful-operation premise is supplied by the caller. -/
theorem of_authorization (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) (virtual : rootPosition ≠ 0)
    (support : UniIndex → Prop)
    (authorization : Authorization tree initial protections root rootPosition maximum .Write support)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree initial protections).topology)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let result := tree.performWildcardAccessAt initial root maximum .Write protections true
    result.status = .Completed ∧ ∃ removed,
      Removal tree initial protections maximum .Write removed ∧
      Matches tree initial result.location protections .Write removed ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
      (∀ query, ¬support query → result.location.perms.get query = initial.perms.get query) ∧
      GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
      (∀ query, tree.nodes.get query = none → result.location.perms.get query = initial.perms.get query) := by
  let weights := GeneralBorrowWildcardForestWeights.of_forest tree initial protections forest
  let area := GeneralBorrowWildcardControlStack.Support.of_authorization tree initial protections root rootPosition maximum .Write support authorization
  let plan := DuplicatePrefixResidualWriteWitnessPlan.virtual tree initial protections root rootPosition maximum virtual
  have actual := GeneralBorrowResidualSavedWriteRuntime.access tree initial protections root rootPosition maximum weights
    (GeneralBorrowWildcardForestWeights.bounded tree initial protections forest root) area plan authorization
      depth forest coherent short profile possible
  have virtualEq : (rootPosition != 0) = true := by simp [virtual]
  simpa only [virtualEq,area,GeneralBorrowWildcardControlStack.Support.of_authorization] using actual

end DuplicatePrefix.GeneralBorrowResidualVirtualWriteRuntime
