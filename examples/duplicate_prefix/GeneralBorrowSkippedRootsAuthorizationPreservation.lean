import duplicate_prefix.GeneralBorrowCompatibleSkippedRootsAccess
import duplicate_prefix.DuplicatePrefixNormalAuthorizationPreservation

namespace DuplicatePrefix.GeneralBorrowSkippedRootsAuthorizationPreservation
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection GeneralBorrowExposure
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- One actual stored-row access retains both-kind S01 normal authorization
and raw skip data for all additional virtual roots. This is a next-access
capability on the resulting row, with the same tree/protections; it does not
assert preservation by constructors or install the row into the tree. -/
theorem of_call_authorization_at (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (position : Nat) (valid : position < tree.locations.entries.size)
    (anchor selected : UniIndex) (anchorNode selectedNode : TreeNode) (extras : List UniIndex)
    (authorization : DuplicatePrefixBorrowAuthorization.Normal tree
      tree.locations.entries[position].data global.protectedTags anchor)
    (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (selectedPresent : tree.nodes.get selected = some selectedNode)
    (roots : tree.roots = (selected :: extras).toArray)
    (different : ∀ root ∈ extras, root ≠ selected)
    (rootPath : ((source_normal_projection tree tree.locations.entries[position].data global.protectedTags).topology.ancestorPath anchor.toNat).getLast! = selected.toNat)
    (raw : ∀ root ∈ extras, ∃ node, tree.nodes.get root = some node ∧
      ¬ authorization.component.support root.toNat ∧ selectedNode.tag.value < node.tag.value ∧
      GeneralBorrowNewerVirtualRootSkip.Raw (GeneralBorrowWildcardVirtualLeaf.effective tree.locations.entries[position].data root node))
    (kind : AccessKind) (range : ByteRange) :
    let after := source_access_location (source_tree_access_at tree tree.locations.entries[position].data
      (some anchor) kind global.protectedTags .VisitChildrenOfAccessed range)
    source_access_status (source_tree_access_at tree tree.locations.entries[position].data
      (some anchor) kind global.protectedTags .VisitChildrenOfAccessed range) = none ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree after global.protectedTags ∧
    (∃ next : DuplicatePrefixBorrowAuthorization.Normal tree after global.protectedTags anchor,
      next.component = authorization.component ∧
    (∀ root ∈ extras, ∃ node, tree.nodes.get root = some node ∧
      ¬ next.component.support root.toNat ∧ selectedNode.tag.value < node.tag.value ∧
      GeneralBorrowNewerVirtualRootSkip.Raw (GeneralBorrowWildcardVirtualLeaf.effective after root node))) := by
  let location := tree.locations.entries[position].data
  obtain ⟨forest⟩ := runtime.formed.forest location global.protectedTags
  obtain ⟨depth⟩ := runtime.formed.depth
  have owned : GeneralBorrowCompatibleScopedNormal.Owned
      (source_normal_projection tree location global.protectedTags) anchor.toNat kind authorization.component := by
    intro index supported bounded
    have size : (source_normal_projection tree location global.protectedTags).topology.nodes.size = tree.nodes.data.size := by
      unfold_general_projection
      unfold_general_topology
      simp only [Array.size_map]
    exact authorization.permissions kind index supported (by rw [←size];exact bounded)
  have actual := GeneralBorrowCompatibleSkippedRootsAccess.access tree location global.protectedTags
    anchor selected anchorNode selectedNode extras kind range forest authorization.component owned depth runtime.formed.children
    anchorPresent selectedPresent roots different rootPath (runtime.coherent position valid) raw
  have geometry := GeneralBorrowExposedScopedNormalMetadata.valid_aligned tree location global.protectedTags anchor anchorNode anchorPresent
  obtain ⟨next,same⟩ := DuplicatePrefixNormalAuthorizationPreservation.normal_preserves_component
    tree location global.protectedTags anchor kind .VisitChildrenOfAccessed runtime.formed.fits forest geometry.1 authorization
  refine ⟨actual.2.1,actual.2.2,?_⟩
  rw [actual.1]
  refine ⟨next,same,?_⟩
  intro root member
  obtain ⟨node,present,separate,newer,state⟩ := raw root member
  have stored := GeneralBorrowExposedScopedNormalCache.outside tree location global.protectedTags anchor kind .VisitChildrenOfAccessed
    authorization.component root node present separate
  exact ⟨node,present,by rw [same];exact separate,newer,by
    simpa only [GeneralBorrowWildcardVirtualLeaf.effective,stored] using state⟩

end DuplicatePrefix.GeneralBorrowSkippedRootsAuthorizationPreservation
