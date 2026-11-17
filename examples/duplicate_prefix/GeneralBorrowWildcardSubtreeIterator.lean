import duplicate_prefix.GeneralBorrowWildcardSubtreeRegionFold
import duplicate_prefix.GeneralBorrowTwoRootNormalAccess
import duplicate_prefix.GeneralBorrowNormalEventCacheFrame

namespace DuplicatePrefix.GeneralBorrowWildcardSubtreeIterator
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowWildcardSubtreeRegion
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

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

/-- The real interpreter source access performs its actual normal access,
then any finite initial list of unexposed extra subtrees in source order.
Common child-closed ForeignOwned support and zero counters suffice. Normal
visitors are unexposed and outside the region, yielding its derived starting
owner/cache frame; no traversal or operation-success premise is provided. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor primary : UniIndex) (anchorNode primaryNode : TreeNode)
    (extras : List UniIndex) (kind : AccessKind) (range : ByteRange)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location protections) anchor.toNat kind)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (primaryPresent : tree.nodes.get primary = some primaryNode)
    (roots : tree.roots = (primary :: extras).toArray)
    (different : ∀ root ∈ extras, root ≠ primary)
    (rootPath : ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast! = primary.toNat)
    (region : Region tree location kind protections) (supported : ∀ root ∈ extras, region.support root)
    (outside : ∀ query, region.support query →
      ∀ event ∈ ((source_normal_projection tree location protections).topology.traverse anchor.toNat .VisitChildrenOfAccessed
        (sourceNormalSkipped (source_normal_projection tree location protections) kind)).2, event.node ≠ query.toNat)
    (normalUnexposed : ∀ event ∈ ((source_normal_projection tree location protections).performAccess anchor.toNat kind .VisitChildrenOfAccessed).visited,
      ∀ index node, UniIndex.ofNat? event.node = some index → tree.nodeAt index = some node → node.isExposed = false) :
    ∃ after,
      source_access_location (source_tree_access_at tree location (some anchor) kind protections .VisitChildrenOfAccessed range) = after ∧
      source_access_status (source_tree_access_at tree location (some anchor) kind protections .VisitChildrenOfAccessed range) = none ∧
      Owned region after ∧ after.exposedCache = location.exposedCache ∧
      (∀ query, ¬region.support query → after.perms.get query =
        (tree.performNormalAccessAt location anchor kind protections .VisitChildrenOfAccessed).location.perms.get query) := by
  have normalGood := GeneralBorrowNormalLocation.normal_succeeds tree location protections anchor kind
    .VisitChildrenOfAccessed forest owned depth children anchorNode anchorPresent
  have normalRootEq : (tree.performNormalAccessAt location anchor kind protections .VisitChildrenOfAccessed).access.root = primary.toNat :=
    (GeneralBorrowStorage.events_root _ _ kind (source_normal_projection tree location protections)).trans rootPath
  have converted : UniIndex.ofNat? (tree.performNormalAccessAt location anchor kind protections .VisitChildrenOfAccessed).access.root = some primary := by
    rw [normalRootEq]
    exact index_self primary
  let middle := (tree.performNormalAccessAt location anchor kind protections .VisitChildrenOfAccessed).location
  have middleOwned : Owned region middle := by
    intro query node member present
    have lookup := GeneralBorrowTwoRootNormalAccess.normal_unvisited tree location protections anchor query node kind .VisitChildrenOfAccessed
      present (outside query member)
    dsimp only [middle]
    simpa only [GeneralBorrowWildcardVirtualLeaf.effective,lookup] using region.owned query node member present
  have middleCache : middle.exposedCache = location.exposedCache :=
    GeneralBorrowNormalEventCacheFrame.normal_cache tree location anchor kind protections .VisitChildrenOfAccessed normalUnexposed
  let middleRegion := rebase region middle middleOwned middleCache
  obtain ⟨after,completed,preserved,cache,frame⟩ := GeneralBorrowWildcardSubtreeRegionFold.access tree middle kind protections forest
    middleRegion extras (some primaryNode.tag) supported
  obtain ⟨actual,status⟩ := iterator tree location after anchor primary primaryNode extras kind protections range
    normalGood.1 normalGood.2 converted primaryPresent roots different completed
  exact ⟨after,actual,status,preserved,cache.trans middleCache,frame⟩

end DuplicatePrefix.GeneralBorrowWildcardSubtreeIterator
