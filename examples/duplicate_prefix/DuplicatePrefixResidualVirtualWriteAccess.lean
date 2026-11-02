import duplicate_prefix.DuplicatePrefixResidualVirtualWriteDFS
namespace DuplicatePrefix.DuplicatePrefixResidualVirtualWriteAccess
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixResidualSupportAuthorization DuplicatePrefixResidualCountModel
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Raw S01 query-pair authorization supplies the actual virtual Write DFS on
an arbitrary finite forest. The legal removal mask is produced internally by
real node transitions, and all unsupported physical permission slots survive.
No profile, noFree, leaf shape, special tag order or operation-success input
is used. This is one real callback, not a whole function. -/
theorem of_authorization (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) (virtual : rootPosition ≠ 0)
    (support : UniIndex → Prop)
    (authorization : Authorization tree initial protections root rootPosition maximum .Write support)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree initial protections).topology)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536) :
    let result := tree.performWildcardAccessAt initial root maximum .Write protections true
    result.status = .Completed ∧ ∃ removed,
      Removal tree initial protections maximum .Write removed ∧
      Matches tree initial result.location protections .Write removed ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
      (∀ query, ¬support query → result.location.perms.get query = initial.perms.get query) := by
  let weights := GeneralBorrowWildcardForestWeights.of_forest tree initial protections forest
  let area := GeneralBorrowWildcardControlStack.Support.of_authorization tree initial protections root rootPosition maximum .Write support authorization
  have actual := DuplicatePrefixResidualVirtualWriteDFS.access tree initial protections root rootPosition maximum virtual weights
    (GeneralBorrowWildcardForestWeights.bounded tree initial protections forest root) area authorization depth forest coherent short
  have virtualEq : (rootPosition != 0) = true := by simp [virtual]
  simpa only [virtualEq,area,GeneralBorrowWildcardControlStack.Support.of_authorization] using actual
end DuplicatePrefix.DuplicatePrefixResidualVirtualWriteAccess
