import duplicate_prefix.GeneralBorrowWildcardSubtreeComplete
import duplicate_prefix.GeneralBorrowWildcardForestWeights

namespace DuplicatePrefix.GeneralBorrowWildcardSubtreeSafety
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess
open GeneralBorrowWildcardSubtreeData GeneralBorrowWildcardSubtreeState

/-- Actual unexposed virtual-subtree access on an arbitrary finite valid forest.
Foreign ownership, zero selected-kind cache counters and graph support are
initial data. Descendant cardinalities derive the original source loop bound;
no operation success or externally supplied traversal budget is assumed. -/
theorem access (tree : BorrowTree) (initial : LocationTree) (root : UniIndex)
    (maximum : Option BorTag) (kind : AccessKind) (protections : ProtectedTags)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree initial protections).topology)
    (data : Data tree initial root kind protections) :
    let result := tree.performWildcardAccessAt initial root maximum kind protections true
    result.status = .Completed ∧ Owned data result.location ∧
      result.location.exposedCache = initial.exposedCache ∧
      (∀ query, ¬data.support query → result.location.perms.get query = initial.perms.get query) :=
  GeneralBorrowWildcardSubtreeComplete.access tree initial root maximum kind protections
    (GeneralBorrowWildcardForestWeights.of_forest tree initial protections forest)
    (GeneralBorrowWildcardForestWeights.bounded tree initial protections forest root) data

end DuplicatePrefix.GeneralBorrowWildcardSubtreeSafety
