import duplicate_prefix.GeneralBorrowExposedVirtualSchedule
import duplicate_prefix.GeneralBorrowNormalExposureCache
import duplicate_prefix.GeneralBorrowTwoRootNormalAccess

namespace DuplicatePrefix.GeneralBorrowExposedForestAccess
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
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

/-- The complete physical source operation, with a concrete primary root at
position zero followed by any finite exposed supporting leaf-root schedule.
Initial normal ownership derives its successful prefix, and coherent exposure
counts derive every extra root's Either branch. Only normal events are required
unexposed; the extra leaves are explicitly exposed. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor primary : UniIndex) (anchorNode primaryNode : TreeNode)
    (extras : List UniIndex) (nodes : UniIndex → TreeNode) (kind : AccessKind) (range : ByteRange)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location protections) anchor.toNat kind)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (primaryPresent : tree.nodes.get primary = some primaryNode)
    (roots : tree.roots = (primary :: extras).toArray)
    (different : ∀ root ∈ extras, root ≠ primary)
    (rootPath : ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast! = primary.toNat)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536)
    (data : ∀ root ∈ extras, tree.nodes.get root = some (nodes root) ∧
      (nodes root).children = #[] ∧ (nodes root).isExposed = true ∧
      GeneralBorrowExposureCardinality.supports
        (GeneralBorrowExposureCardinality.effective location protections root (nodes root)) kind = true ∧
      GeneralBorrowWildcardVirtualLeaf.onlyForeign (nodes root) (some primaryNode.tag) = false)
    (unexposed : ∀ event ∈ ((source_normal_projection tree location protections).performAccess
        anchor.toNat kind .VisitChildrenOfAccessed).visited, ∀ index node,
      UniIndex.ofNat? event.node = some index → tree.nodeAt index = some node → node.isExposed = false) :
    ∃ after,
      source_access_location (source_tree_access_at tree location (some anchor) kind protections .VisitChildrenOfAccessed range) = after ∧
      source_access_status (source_tree_access_at tree location (some anchor) kind protections .VisitChildrenOfAccessed range) = none ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree after protections ∧
      after.exposedCache = location.exposedCache ∧
      (∀ query node, tree.nodes.get query = some node →
        GeneralBorrowWildcardVirtualLeaf.effective after query node =
        GeneralBorrowWildcardVirtualLeaf.effective
          (tree.performNormalAccessAt location anchor kind protections .VisitChildrenOfAccessed).location query node) := by
  have normal := GeneralBorrowNormalExposureCache.access tree location protections anchor kind .VisitChildrenOfAccessed
    depth children anchorNode anchorPresent forest owned coherent
  have rootEq : (tree.performNormalAccessAt location anchor kind protections .VisitChildrenOfAccessed).access.root = primary.toNat :=
    (GeneralBorrowStorage.events_root _ _ kind (source_normal_projection tree location protections)).trans rootPath
  have converted : UniIndex.ofNat? (tree.performNormalAccessAt location anchor kind protections .VisitChildrenOfAccessed).access.root = some primary := by
    rw [rootEq]; exact index_self primary
  have visited := GeneralBorrowStorage.events_visited
    ((source_normal_projection tree location protections).topology.traverse anchor.toNat .VisitChildrenOfAccessed
      (sourceNormalSkipped (source_normal_projection tree location protections) kind)).2
    ((source_normal_projection tree location protections).topology.traverse anchor.toNat .VisitChildrenOfAccessed
      (sourceNormalSkipped (source_normal_projection tree location protections) kind)).1
    kind (source_normal_projection tree location protections) normal.1
  change ((source_normal_projection tree location protections).performAccess anchor.toNat kind .VisitChildrenOfAccessed).visited =
    ((source_normal_projection tree location protections).topology.traverse anchor.toNat .VisitChildrenOfAccessed
      (sourceNormalSkipped (source_normal_projection tree location protections) kind)).2 at visited
  let middle := (tree.performNormalAccessAt location anchor kind protections .VisitChildrenOfAccessed).location
  have cache : middle.exposedCache = location.exposedCache :=
    GeneralBorrowNormalEventCacheFrame.normal_cache tree location anchor kind protections .VisitChildrenOfAccessed unexposed
  have afterData : ∀ root ∈ extras, tree.nodes.get root = some (nodes root) ∧
      (nodes root).children = #[] ∧ (nodes root).isExposed = true ∧
      GeneralBorrowExposureCardinality.supports
        (GeneralBorrowExposureCardinality.effective middle protections root (nodes root)) kind = true ∧
      GeneralBorrowWildcardVirtualLeaf.onlyForeign (nodes root) (some primaryNode.tag) = false := by
    intro root member
    obtain ⟨present,leaf,exposed,support,cutoff⟩ := data root member
    have outside : ∀ event ∈ ((source_normal_projection tree location protections).topology.traverse anchor.toNat
        .VisitChildrenOfAccessed (sourceNormalSkipped (source_normal_projection tree location protections) kind)).2,
        event.node ≠ root.toNat := by
      intro event eventMember same
      have eventActual : event ∈ ((source_normal_projection tree location protections).performAccess anchor.toNat kind .VisitChildrenOfAccessed).visited := by
        rw [visited]; exact eventMember
      have conversion : UniIndex.ofNat? event.node = some root := by rw [same]; exact index_self root
      have flag := unexposed event eventActual root (nodes root) conversion present
      rw [exposed] at flag
      cases flag
    have stored := GeneralBorrowTwoRootNormalAccess.normal_unvisited tree location protections anchor root (nodes root)
      kind .VisitChildrenOfAccessed present outside
    refine ⟨present,leaf,exposed,?_,cutoff⟩
    simpa only [GeneralBorrowExposureCardinality.effective,show middle.perms.get root = location.perms.get root from stored] using support
  obtain ⟨after,completed,afterCache,frame⟩ := GeneralBorrowExposedVirtualSchedule.schedule tree middle protections extras nodes
    (some primaryNode.tag) kind normal.2.2 short afterData
  obtain ⟨actual,status⟩ := iterator tree location after anchor primary primaryNode extras kind protections range
    normal.1 normal.2.1 converted primaryPresent roots different completed
  exact ⟨after,actual,status,GeneralBorrowExposedVirtualSchedule.coherent_frame tree middle after protections
    normal.2.2 afterCache frame,afterCache.trans cache,frame⟩

/-- A fully exposed primary component is permitted when raw normal-event
geometry excludes the extra roots. Its genuine normal cache updates are
retained, rather than assumed absent. All extra calls preserve those counters. -/
theorem access_exposed_primary (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor primary : UniIndex) (anchorNode primaryNode : TreeNode)
    (extras : List UniIndex) (nodes : UniIndex → TreeNode) (kind : AccessKind) (range : ByteRange)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location protections) anchor.toNat kind)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (primaryPresent : tree.nodes.get primary = some primaryNode)
    (roots : tree.roots = (primary :: extras).toArray)
    (different : ∀ root ∈ extras, root ≠ primary)
    (rootPath : ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast! = primary.toNat)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536)
    (data : ∀ root ∈ extras, tree.nodes.get root = some (nodes root) ∧
      (nodes root).children = #[] ∧ (nodes root).isExposed = true ∧
      GeneralBorrowExposureCardinality.supports
        (GeneralBorrowExposureCardinality.effective location protections root (nodes root)) kind = true ∧
      GeneralBorrowWildcardVirtualLeaf.onlyForeign (nodes root) (some primaryNode.tag) = false)
    (outside : ∀ root ∈ extras, ∀ event ∈
      ((source_normal_projection tree location protections).topology.traverse anchor.toNat .VisitChildrenOfAccessed
        (sourceNormalSkipped (source_normal_projection tree location protections) kind)).2,
      event.node ≠ root.toNat) :
    ∃ after,
      source_access_location (source_tree_access_at tree location (some anchor) kind protections .VisitChildrenOfAccessed range) = after ∧
      source_access_status (source_tree_access_at tree location (some anchor) kind protections .VisitChildrenOfAccessed range) = none ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree after protections ∧
      after.exposedCache =
        (tree.performNormalAccessAt location anchor kind protections .VisitChildrenOfAccessed).location.exposedCache ∧
      (∀ query node, tree.nodes.get query = some node →
        GeneralBorrowWildcardVirtualLeaf.effective after query node =
        GeneralBorrowWildcardVirtualLeaf.effective
          (tree.performNormalAccessAt location anchor kind protections .VisitChildrenOfAccessed).location query node) := by
  have normal := GeneralBorrowNormalExposureCache.access tree location protections anchor kind .VisitChildrenOfAccessed
    depth children anchorNode anchorPresent forest owned coherent
  have rootEq : (tree.performNormalAccessAt location anchor kind protections .VisitChildrenOfAccessed).access.root = primary.toNat :=
    (GeneralBorrowStorage.events_root _ _ kind (source_normal_projection tree location protections)).trans rootPath
  have converted : UniIndex.ofNat? (tree.performNormalAccessAt location anchor kind protections .VisitChildrenOfAccessed).access.root = some primary := by
    rw [rootEq]; exact index_self primary
  let middle := (tree.performNormalAccessAt location anchor kind protections .VisitChildrenOfAccessed).location
  have afterData : ∀ root ∈ extras, tree.nodes.get root = some (nodes root) ∧
      (nodes root).children = #[] ∧ (nodes root).isExposed = true ∧
      GeneralBorrowExposureCardinality.supports
        (GeneralBorrowExposureCardinality.effective middle protections root (nodes root)) kind = true ∧
      GeneralBorrowWildcardVirtualLeaf.onlyForeign (nodes root) (some primaryNode.tag) = false := by
    intro root member
    obtain ⟨present,leaf,exposed,support,cutoff⟩ := data root member
    have stored := GeneralBorrowTwoRootNormalAccess.normal_unvisited tree location protections anchor root (nodes root)
      kind .VisitChildrenOfAccessed present (outside root member)
    refine ⟨present,leaf,exposed,?_,cutoff⟩
    simpa only [GeneralBorrowExposureCardinality.effective,show middle.perms.get root = location.perms.get root from stored] using support
  obtain ⟨after,completed,afterCache,frame⟩ := GeneralBorrowExposedVirtualSchedule.schedule tree middle protections extras nodes
    (some primaryNode.tag) kind normal.2.2 short afterData
  obtain ⟨actual,status⟩ := iterator tree location after anchor primary primaryNode extras kind protections range
    normal.1 normal.2.1 converted primaryPresent roots different completed
  exact ⟨after,actual,status,GeneralBorrowExposedVirtualSchedule.coherent_frame tree middle after protections
    normal.2.2 afterCache frame,afterCache,frame⟩
end DuplicatePrefix.GeneralBorrowExposedForestAccess
