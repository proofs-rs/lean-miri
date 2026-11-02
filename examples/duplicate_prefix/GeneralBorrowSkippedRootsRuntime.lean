import duplicate_prefix.GeneralBorrowSkippedRootsAuthorizationPreservation
import duplicate_prefix.GeneralBorrowCompatibleNormalRuntime
namespace DuplicatePrefix.GeneralBorrowSkippedRootsRuntime
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection GeneralBorrowExposure
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Installing the actual full-access row preserves complete RuntimeFacts.
All other-root callbacks are derived no-ops; row installation is explicit. -/
theorem after_row (tree : BorrowTree) (global : GlobalState)
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
    let result := source_tree_access_at tree tree.locations.entries[position].data
      (some anchor) kind global.protectedTags .VisitChildrenOfAccessed range
    source_access_status result = none ∧
    DuplicatePrefixBorrowContract.RuntimeFacts
      {tree with locations := GeneralRangeMapState.replaced tree.locations position valid (source_access_location result)} global := by
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
  have normal := GeneralBorrowCompatibleNormalRuntime.after_row tree global runtime position valid
    anchor authorization anchorNode anchorPresent kind .VisitChildrenOfAccessed
  refine ⟨actual.2.1,?_⟩
  change DuplicatePrefixBorrowContract.RuntimeFacts
    {tree with locations := GeneralRangeMapState.replaced tree.locations position valid (source_access_location (source_tree_access_at tree location (some anchor) kind global.protectedTags .VisitChildrenOfAccessed range))} global
  rw [actual.1]
  exact normal.2.2

end DuplicatePrefix.GeneralBorrowSkippedRootsRuntime
