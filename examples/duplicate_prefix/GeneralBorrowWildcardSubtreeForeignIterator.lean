import duplicate_prefix.GeneralBorrowForeignOwnerRegion
import duplicate_prefix.GeneralBorrowUnexposedMin
import duplicate_prefix.GeneralBorrowWildcardSubtreeRegionFold
import duplicate_prefix.GeneralBorrowTwoRootNormalAccess
import duplicate_prefix.GeneralBorrowNormalEventCacheFrame

namespace DuplicatePrefix.GeneralBorrowWildcardSubtreeForeignIterator
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowWildcardSubtreeRegion
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

private theorem iterator (tree : BorrowTree) (location after : LocationTree)
    (anchor primary : UniIndex) (primaryNode : TreeNode) (extras : List UniIndex)
    (kind : AccessKind) (protections : ProtectedTags) (mode : ChildrenVisitMode) (range : ByteRange)
    (normalStatus : (tree.performNormalAccessAt location anchor kind protections mode).access.status = .Completed)
    (normalOutcome : (tree.performNormalAccessAt location anchor kind protections mode).outcome = .ok ())
    (converted : UniIndex.ofNat? (tree.performNormalAccessAt location anchor kind protections mode).access.root = some primary)
    (primaryPresent : tree.nodes.get primary = some primaryNode)
    (roots : tree.roots = (primary :: extras).toArray)
    (minimum : source_min_exposed tree anchor = none)
    (different : ∀ root ∈ extras, root ≠ primary)
    (completed : GeneralBorrowWildcardVirtualLeafFold.run tree extras
      (tree.performNormalAccessAt location anchor kind protections mode).location
      (some primaryNode.tag) kind protections = ⟨after,.Completed⟩) :
    source_access_location (source_tree_access_at tree location (some anchor) kind protections mode range) = after ∧
    source_access_status (source_tree_access_at tree location (some anchor) kind protections mode range) = none := by
  simp_tree_helpers
  simp only [normalStatus,normalOutcome,converted,primaryPresent,roots]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one,List.size_toArray,List.length_cons]
  simp [primaryPresent,minimum,List.size_toArray,List.range'_succ,bind,pure]
  change (forIn (List.range' 1 extras.length)
    ((tree.performNormalAccessAt location anchor kind protections mode).location,none,false)
    (GeneralBorrowVirtualRootsAdapter.scanAt tree primary extras primaryNode.tag kind protections range)).1 = after ∧
    (forIn (List.range' 1 extras.length)
    ((tree.performNormalAccessAt location anchor kind protections mode).location,none,false)
    (GeneralBorrowVirtualRootsAdapter.scanAt tree primary extras primaryNode.tag kind protections range)).2.1 = none
  rw [GeneralBorrowVirtualRootsAdapter.indexed]
  rw [GeneralBorrowVirtualRootsAdapter.successful tree primary primaryNode.tag kind protections range extras different _ after completed]
  exact ⟨rfl,rfl⟩

/-- The real interpreter source access, in either normal-visitor mode, performs its actual normal access,
then any finite initial list of unexposed extra subtrees in source order.
Common child-closed ForeignOwned support and zero counters suffice. Graph-only
foreignness replaces visitor exclusion: actual normal ownership preservation
derives the region's post-Read/Write ownership even if it was visited. All nodes
are initially unexposed, yielding the exact cache frame. Static unexposed flags derive the actual minimum-exposure
search result, so SkipChildrenOfAccessed cannot stop this root schedule early.
No traversal or operation-success premise is provided. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor primary : UniIndex) (anchorNode primaryNode : TreeNode)
    (extras : List UniIndex) (kind : AccessKind) (mode : ChildrenVisitMode) (range : ByteRange)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location protections) anchor.toNat kind)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (primaryPresent : tree.nodes.get primary = some primaryNode)
    (roots : tree.roots = (primary :: extras).toArray)
    (different : ∀ root ∈ extras, root ≠ primary)
    (rootPath : ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast! = primary.toNat)
    (region : Region tree location kind protections) (supported : ∀ root ∈ extras, region.support root)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (foreignGraph : ∀ query, region.support query →
      query.toNat ∉ (source_normal_projection tree location protections).topology.ancestorPath anchor.toNat)
    (allUnexposed : ∀ index node, tree.nodes.get index = some node → node.isExposed = false) :
    ∃ after,
      source_access_location (source_tree_access_at tree location (some anchor) kind protections mode range) = after ∧
      source_access_status (source_tree_access_at tree location (some anchor) kind protections mode range) = none ∧
      Owned region after ∧ after.exposedCache = location.exposedCache ∧
      (∀ query, ¬region.support query → after.perms.get query =
        (tree.performNormalAccessAt location anchor kind protections mode).location.perms.get query) := by
  have normalUnexposed : ∀ event ∈ ((source_normal_projection tree location protections).performAccess anchor.toNat kind mode).visited,
      ∀ index node, UniIndex.ofNat? event.node = some index → tree.nodeAt index = some node → node.isExposed = false :=
    fun event member index node conversion present => allUnexposed index node present
  have minimum := GeneralBorrowUnexposedMin.min_none tree anchor allUnexposed
  have normalGood := GeneralBorrowNormalLocation.normal_succeeds tree location protections anchor kind
    mode forest owned depth children anchorNode anchorPresent
  have normalRootEq : (tree.performNormalAccessAt location anchor kind protections mode).access.root = primary.toNat :=
    (GeneralBorrowStorage.events_root _ _ kind (source_normal_projection tree location protections)).trans rootPath
  have converted : UniIndex.ofNat? (tree.performNormalAccessAt location anchor kind protections mode).access.root = some primary := by
    rw [normalRootEq]
    exact index_self primary
  let middle := (tree.performNormalAccessAt location anchor kind protections mode).location
  have normalOwner := GeneralBorrowRangePreserves.normal_location_owned tree location protections anchor kind mode fits forest owned
  have middleOwned : Owned region middle := by
    intro query node member present
    exact GeneralBorrowForeignOwnerRegion.foreign tree middle protections anchor query node kind present normalOwner
      (foreignGraph query member)
  have middleCache : middle.exposedCache = location.exposedCache :=
    GeneralBorrowNormalEventCacheFrame.normal_cache tree location anchor kind protections mode normalUnexposed
  let middleRegion := rebase region middle middleOwned middleCache
  obtain ⟨after,completed,preserved,cache,frame⟩ := GeneralBorrowWildcardSubtreeRegionFold.access tree middle kind protections forest
    middleRegion extras (some primaryNode.tag) supported
  obtain ⟨actual,status⟩ := iterator tree location after anchor primary primaryNode extras kind protections mode range
    normalGood.1 normalGood.2 converted primaryPresent roots minimum different completed
  exact ⟨after,actual,status,preserved,cache.trans middleCache,frame⟩

end DuplicatePrefix.GeneralBorrowWildcardSubtreeForeignIterator
