import duplicate_prefix.GeneralBorrowExposedKnownRootWriteInvariant
import duplicate_prefix.GeneralBorrowExposedNonleafPrimaryPath
namespace DuplicatePrefix.GeneralBorrowExposedKnownRootWritePrimaryPath
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedKnownRootWriteState
open GeneralBorrowExposedNonleafPrimaryPath

open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]

theorem positive {tree initial root protections} (data : Data tree initial root protections)
    (witness : UniIndex) (node : TreeNode) (present : tree.nodes.get witness = some node)
    (exposed : node.isExposed = true)
    (support : GeneralBorrowExposureCardinality.supports (GeneralBorrowExposureCardinality.effective initial protections witness node) .Write = true)
    (index : UniIndex) (path : Path tree index witness) :
    0 < GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache index .Write :=
  GeneralBorrowExposedConditionalAccessSupport.exposed_descendant tree initial protections data.coherent data.short .Write index witness node
    present exposed support (path.walk data.depth)
end DuplicatePrefix.GeneralBorrowExposedKnownRootWritePrimaryPath
