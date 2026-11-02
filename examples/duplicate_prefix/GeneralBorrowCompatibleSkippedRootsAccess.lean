import duplicate_prefix.GeneralBorrowNewerVirtualRootSkip
import duplicate_prefix.GeneralBorrowCompatibleScopedNormalExposure
import duplicate_prefix.GeneralBorrowVirtualRootsAdapter
import duplicate_prefix.GeneralBorrowExposedScopedNormalCache

namespace DuplicatePrefix.GeneralBorrowCompatibleSkippedRootsAccess
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection GeneralBorrowExposure
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem iterator (tree : BorrowTree) (location after : LocationTree)
    (anchor primary : UniIndex) (primaryNode : TreeNode) (extras : List UniIndex)
    (kind : AccessKind) (protections : ProtectedTags) (range : ByteRange)
    (normalStatus : (tree.performNormalAccessAt location anchor kind protections .VisitChildrenOfAccessed).access.status = .Completed)
    (normalOutcome : (tree.performNormalAccessAt location anchor kind protections .VisitChildrenOfAccessed).outcome = .ok ())
    (converted : UniIndex.ofNat? (tree.performNormalAccessAt location anchor kind protections .VisitChildrenOfAccessed).access.root = some primary)
    (primaryPresent : tree.nodes.get primary = some primaryNode)
    (roots : tree.roots = (primary :: extras).toArray)
    (different : ∀ root ∈ extras, root ≠ primary)
    (completed : GeneralBorrowWildcardVirtualLeafFold.run tree extras
      (tree.performNormalAccessAt location anchor kind protections .VisitChildrenOfAccessed).location
      (some primaryNode.tag) kind protections = ⟨after,.Completed⟩) :
    source_access_location (source_tree_access_at tree location (some anchor) kind protections .VisitChildrenOfAccessed range) = after ∧
    source_access_status (source_tree_access_at tree location (some anchor) kind protections .VisitChildrenOfAccessed range) = none := by
  simp_tree_helpers
  simp only [normalStatus,normalOutcome,converted,primaryPresent,roots]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one,List.size_toArray,List.length_cons]
  simp [primaryPresent,List.size_toArray,List.range'_succ,bind,pure]
  change (forIn (List.range' 1 extras.length)
    ((tree.performNormalAccessAt location anchor kind protections .VisitChildrenOfAccessed).location,none,false)
    (GeneralBorrowVirtualRootsAdapter.scanAt tree primary extras primaryNode.tag kind protections range)).1 = after ∧
    (forIn (List.range' 1 extras.length)
    ((tree.performNormalAccessAt location anchor kind protections .VisitChildrenOfAccessed).location,none,false)
    (GeneralBorrowVirtualRootsAdapter.scanAt tree primary extras primaryNode.tag kind protections range)).2.1 = none
  rw [GeneralBorrowVirtualRootsAdapter.indexed]
  rw [GeneralBorrowVirtualRootsAdapter.successful tree primary primaryNode.tag kind protections range extras different _ after completed]
  exact ⟨rfl,rfl⟩

/-- Actual concrete access with any finite list of newer statically skipped
virtual roots. Descendants and permissions below those roots are unrestricted.
The selected component uses exact scalar compatibility, and all completion
facts follow from initial state data. This is an access lemma, not a whole-call
coverage claim. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected : UniIndex) (anchorNode selectedNode : TreeNode) (extras : List UniIndex)
    (kind : AccessKind) (range : ByteRange)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (component : GeneralBorrowExposedScopedNormal.Component (source_normal_projection tree location protections).topology anchor.toNat)
    (owned : GeneralBorrowCompatibleScopedNormal.Owned (source_normal_projection tree location protections) anchor.toNat kind component)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (selectedPresent : tree.nodes.get selected = some selectedNode)
    (roots : tree.roots = (selected :: extras).toArray)
    (different : ∀ root ∈ extras, root ≠ selected)
    (rootPath : ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast! = selected.toNat)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (raw : ∀ root ∈ extras, ∃ node, tree.nodes.get root = some node ∧
      ¬ component.support root.toNat ∧ selectedNode.tag.value < node.tag.value ∧
      GeneralBorrowNewerVirtualRootSkip.Raw (GeneralBorrowWildcardVirtualLeaf.effective location root node)) :
    source_access_location (source_tree_access_at tree location (some anchor) kind protections .VisitChildrenOfAccessed range) =
      (tree.performNormalAccessAt location anchor kind protections .VisitChildrenOfAccessed).location ∧
    source_access_status (source_tree_access_at tree location (some anchor) kind protections .VisitChildrenOfAccessed range) = none ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree
      (source_access_location (source_tree_access_at tree location (some anchor) kind protections .VisitChildrenOfAccessed range)) protections := by
  have normal := GeneralBorrowCompatibleScopedNormalExposure.access tree location protections anchor kind .VisitChildrenOfAccessed
    depth children anchorNode anchorPresent forest component owned coherent
  have rootEq : (tree.performNormalAccessAt location anchor kind protections .VisitChildrenOfAccessed).access.root = selected.toNat :=
    (GeneralBorrowStorage.events_root _ _ kind (source_normal_projection tree location protections)).trans rootPath
  have afterRaw : ∀ root ∈ extras, ∃ node, tree.nodes.get root = some node ∧
      selectedNode.tag.value < node.tag.value ∧ GeneralBorrowNewerVirtualRootSkip.Raw
        (GeneralBorrowWildcardVirtualLeaf.effective (tree.performNormalAccessAt location anchor kind protections .VisitChildrenOfAccessed).location root node) := by
    intro root member
    obtain ⟨node,present,separate,newer,state⟩ := raw root member
    have stored := GeneralBorrowExposedScopedNormalCache.outside tree location protections anchor kind .VisitChildrenOfAccessed
      component root node present separate
    exact ⟨node,present,newer,by simpa only [GeneralBorrowWildcardVirtualLeaf.effective,stored] using state⟩
  have completed := GeneralBorrowNewerVirtualRootSkip.fold tree
    (tree.performNormalAccessAt location anchor kind protections .VisitChildrenOfAccessed).location extras
    selectedNode.tag kind protections afterRaw
  have converted : UniIndex.ofNat? (tree.performNormalAccessAt location anchor kind protections .VisitChildrenOfAccessed).access.root = some selected := by
    rw [rootEq]
    exact index_self selected
  have actual := iterator tree location _ anchor selected selectedNode extras kind protections range
    normal.1 normal.2.1 converted selectedPresent roots different completed
  exact ⟨actual.1,actual.2,by rw [actual.1];exact normal.2.2⟩

end DuplicatePrefix.GeneralBorrowCompatibleSkippedRootsAccess
