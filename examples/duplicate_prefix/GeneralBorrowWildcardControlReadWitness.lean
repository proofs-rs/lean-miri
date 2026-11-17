import duplicate_prefix.GeneralBorrowWildcardControlWitness
namespace DuplicatePrefix.GeneralBorrowWildcardControlReadWitness
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowWildcardSubtreeStack
open GeneralBorrowWildcardControlWitness
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- A real Read supporter protects every ancestor on its witness path from
entry skipping when the maximum-tag filter is absent at that ancestor. This
uses physical Read-counter preservation, not a permission ownership profile. -/
theorem path_entry_not_skip (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536)
    (frame : GeneralBorrowExposedNonleafState.ReadFrame initial current)
    (root index witness : UniIndex) (node : TreeNode)
    (present : tree.nodes.get witness = some node) (exposed : node.isExposed = true)
    (supported : GeneralBorrowExposureCardinality.supports
      (GeneralBorrowExposureCardinality.effective initial protections witness node) .Read = true)
    (rootPath : Path tree root witness) (path : Path tree index witness) (state : LocationState) :
    DuplicatePrefixCallbackVisitAuthorization.entrySkip state .Read
      (current.exposedCache.accessRelatedness root index .Read false false) = false := by
  have rootPositive := GeneralBorrowExposedNonleafRead.exposed_descendant tree initial protections coherent short
    root witness node present exposed supported (rootPath.walk depth)
  have positive := GeneralBorrowExposedNonleafRead.exposed_descendant tree initial protections coherent short
    index witness node present exposed supported (path.walk depth)
  have relation := GeneralBorrowExposedNonleafPrimaryState.classify initial current root index frame rootPositive
  have notForeign := GeneralBorrowExposedNonleafPrimaryState.positive_not_foreign initial root index positive
  rw [relation]
  cases related : GeneralBorrowExposedNonleafPrimaryState.related initial root index with
  | LocalAccess => simp [DuplicatePrefixCallbackVisitAuthorization.entrySkip,DuplicatePrefixCallbackAuthorization.skip,AccessRelatedness.isForeign]
  | EitherAccess => rfl
  | ForeignAccess => exact False.elim (notForeign related)

/-- In the no-maximum primary callback, an actual entry skip cannot discard
the remaining witness path. No operation completion is assumed. -/
theorem pop (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536)
    (frame : GeneralBorrowExposedNonleafState.ReadFrame initial current)
    (root index witness : UniIndex) (node : TreeNode)
    (present : tree.nodes.get witness = some node) (exposed : node.isExposed = true)
    (supported : GeneralBorrowExposureCardinality.supports
      (GeneralBorrowExposureCardinality.effective initial protections witness node) .Read = true)
    (rootPath : Path tree root witness) (state : LocationState)
    (stack : Array Task) (post : Bool) (seen : Bool)
    (pending : Pending tree witness seen (stack.push (index,post)))
    (skipped : DuplicatePrefixCallbackVisitAuthorization.entrySkip state .Read
      (current.exposedCache.accessRelatedness root index .Read false false) = true) :
    Pending tree witness seen stack := by
  apply GeneralBorrowWildcardControlWitness.pop stack index post pending
  intro path
  have impossible := path_entry_not_skip tree initial current protections depth coherent short frame
    root index witness node present exposed supported rootPath path state
  rw [skipped] at impossible
  cases impossible

end DuplicatePrefix.GeneralBorrowWildcardControlReadWitness
