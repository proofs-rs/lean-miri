import duplicate_prefix.GeneralBorrowVirtualRootsAdapter
import duplicate_prefix.GeneralBorrowTwoRootNormalAccess

namespace DuplicatePrefix.GeneralBorrowVirtualRootsIterator
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

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

/-- Actual normal access followed by any finite collection of additional
virtual leaf roots. Every operation's completion follows from initial data:
normal topology/ownership, extra-root topology/ownership, and exclusion of
those extra roots from the normal event schedule. No successful operation is
an input to this theorem. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor primary : UniIndex) (anchorNode primaryNode : TreeNode)
    (nodes : UniIndex → TreeNode) (extras : List UniIndex) (kind : AccessKind) (range : ByteRange)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location protections) anchor.toNat kind)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (primaryPresent : tree.nodes.get primary = some primaryNode)
    (roots : tree.roots = (primary :: extras).toArray)
    (different : ∀ root ∈ extras, root ≠ primary)
    (rootPath : ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast! = primary.toNat)
    (leaves : GeneralBorrowWildcardVirtualLeafFold.Leaves tree nodes extras)
    (extraOwned : GeneralBorrowWildcardVirtualLeafFold.Owned nodes extras protections location)
    (outside : ∀ root ∈ extras,
      ∀ event ∈ ((source_normal_projection tree location protections).topology.traverse
        anchor.toNat .VisitChildrenOfAccessed
        (sourceNormalSkipped (source_normal_projection tree location protections) kind)).2,
      event.node ≠ root.toNat) :
    ∃ after,
      source_access_location (source_tree_access_at tree location (some anchor) kind protections .VisitChildrenOfAccessed range) = after ∧
      source_access_status (source_tree_access_at tree location (some anchor) kind protections .VisitChildrenOfAccessed range) = none ∧
      GeneralBorrowWildcardVirtualLeafFold.Owned nodes extras protections after ∧
      (∀ query, query ∉ extras → after.perms.get query =
        (tree.performNormalAccessAt location anchor kind protections .VisitChildrenOfAccessed).location.perms.get query ∧
        after.exposedCache.nodes.get query =
        (tree.performNormalAccessAt location anchor kind protections .VisitChildrenOfAccessed).location.exposedCache.nodes.get query) := by
  have normalGood := GeneralBorrowNormalLocation.normal_succeeds tree location protections anchor kind
    .VisitChildrenOfAccessed forest owned depth children anchorNode anchorPresent
  have normalRootEq : (tree.performNormalAccessAt location anchor kind protections .VisitChildrenOfAccessed).access.root = primary.toNat :=
    (GeneralBorrowStorage.events_root _ _ kind (source_normal_projection tree location protections)).trans rootPath
  have converted : UniIndex.ofNat? (tree.performNormalAccessAt location anchor kind protections .VisitChildrenOfAccessed).access.root = some primary := by
    rw [normalRootEq]
    exact index_self primary
  have middleOwned : GeneralBorrowWildcardVirtualLeafFold.Owned nodes extras protections
      (tree.performNormalAccessAt location anchor kind protections .VisitChildrenOfAccessed).location := by
    intro root member
    have present := (leaves root member).1
    have lookup := GeneralBorrowTwoRootNormalAccess.normal_unvisited tree location protections anchor root
      (nodes root) kind .VisitChildrenOfAccessed present (outside root member)
    simpa only [GeneralBorrowWildcardVirtualLeaf.effective,lookup] using extraOwned root member
  obtain ⟨after,completed,preserved,frame⟩ := GeneralBorrowWildcardVirtualLeafFold.complete tree nodes extras
    (tree.performNormalAccessAt location anchor kind protections .VisitChildrenOfAccessed).location
    (some primaryNode.tag) kind protections depth leaves middleOwned
  obtain ⟨actual,status⟩ := iterator tree location after anchor primary primaryNode extras kind protections range
    normalGood.1 normalGood.2 converted primaryPresent roots different completed
  exact ⟨after,actual,status,preserved,frame⟩

end DuplicatePrefix.GeneralBorrowVirtualRootsIterator
