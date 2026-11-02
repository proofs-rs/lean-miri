import duplicate_prefix.GeneralBorrowExposedScopedLeafWriteData
import duplicate_prefix.GeneralBorrowSparseExposedLeafState
namespace DuplicatePrefix.GeneralBorrowExposedScopedWritableLeafWriteData
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- Stored or lazy effective old-leaf states supply their actual local Write
support; no replacement by Unique is performed. -/
theorem support (location : LocationTree) (protections : ProtectedTags) (index : UniIndex) (node : TreeNode)
    (compatible : GeneralBorrowExposedConditionalWritePermissions.Compatible
      (GeneralBorrowWildcardVirtualLeaf.effective location index node) .LocalAccess (protections.contains node.tag)) :
    GeneralBorrowExposureCardinality.supports (GeneralBorrowExposureCardinality.effective location protections index node) .Write=true :=
  GeneralBorrowSparseExposedLeafState.supports _ _ compatible .Write

/-- Coherent positive self counters classify every old leaf locally for the
real conditional Write dispatcher, with its original mixed permission. -/
theorem profile (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections) (short : tree.nodes.size<65536)
    (states : ∀index node,area.support index→tree.nodes.get index=some node→node.isExposed=true ∧
      GeneralBorrowExposedConditionalWritePermissions.Compatible (GeneralBorrowWildcardVirtualLeaf.effective location index node)
        .LocalAccess (protections.contains node.tag)) :
    GeneralBorrowExposedKnownRootWriteState.Profile tree location protections := by
  intro index node included present
  obtain ⟨exposed,compatible⟩:=states index node included present
  have positive:=GeneralBorrowExposureCardinality.exposed_self location.exposedCache tree.nodes
    (GeneralBorrowExposureCardinality.effective location protections) coherent short index node present exposed .Write
    (support location protections index node compatible)
  change 0<GeneralBorrowWildcardRelatednessBounds.count location.exposedCache index .Write at positive
  have nonzero : GeneralBorrowExposedKnownRootWriteState.zero location index=false := by
    simp [GeneralBorrowExposedKnownRootWriteState.zero,Nat.ne_of_gt positive]
  simpa only [GeneralBorrowExposedConditionalWritePermissions.Condition,nonzero,Bool.false_eq_true,ite_false] using compatible

def primary (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) (root : UniIndex) (node : TreeNode)
    (present : tree.nodes.get root=some node) (leaf : node.children=#[]) (included : area.support root)
    (exposed : node.isExposed=true)
    (compatible : GeneralBorrowExposedConditionalWritePermissions.Compatible (GeneralBorrowWildcardVirtualLeaf.effective location root node)
      .LocalAccess (protections.contains node.tag))
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections) (short : tree.nodes.size<65536)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (profile : GeneralBorrowExposedKnownRootWriteState.Profile tree location protections)
    (graph : GeneralBorrowExposedNonleafPrimaryPath.Reciprocal tree) :
    GeneralBorrowExposedKnownRootWritePrimaryWitness.Data tree location root protections where
  base:=GeneralBorrowExposedScopedLeafWriteData.virtual tree location protections root node present leaf included coherent short depth profile
  graph:=graph
  witness:=root
  node:=node
  present:=present
  exposed:=exposed
  support:=support location protections root node compatible
  path:=.refl root node present
end DuplicatePrefix.GeneralBorrowExposedScopedWritableLeafWriteData
