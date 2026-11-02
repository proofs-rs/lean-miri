import duplicate_prefix.GeneralBorrowExposedConditionalReadInvariant
import duplicate_prefix.GeneralBorrowExposedNonleafPrimaryPath
namespace DuplicatePrefix.GeneralBorrowExposedConditionalReadPrimaryPath
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedConditionalReadState
open GeneralBorrowExposedNonleafPrimaryPath

theorem positive {tree initial root protections} (data : Data tree initial root protections)
    (witness : UniIndex) (node : TreeNode) (present : tree.nodes.get witness = some node)
    (exposed : node.isExposed = true)
    (support : GeneralBorrowExposureCardinality.supports (GeneralBorrowExposureCardinality.effective initial protections witness node) .Read = true)
    (index : UniIndex) (path : Path tree index witness) :
    0 < GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache index .Read :=
  GeneralBorrowExposedNonleafRead.exposed_descendant tree initial protections data.coherent data.short index witness node
    present exposed support (path.walk data.depth)
end DuplicatePrefix.GeneralBorrowExposedConditionalReadPrimaryPath
