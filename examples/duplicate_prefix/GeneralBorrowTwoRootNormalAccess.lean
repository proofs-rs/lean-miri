import duplicate_prefix.GeneralBorrowNormalEventCacheFrame
import duplicate_prefix.GeneralBorrowWildcardLeaf
import duplicate_prefix.GeneralBorrowNormalLocation
namespace DuplicatePrefix.GeneralBorrowTwoRootNormalAccess
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowFreshActiveOnClean DuplicatePrefix.GeneralBorrowEvents DuplicatePrefix.GeneralBorrowStorage
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Actual normal-access writeback retains an existing node's optional stored
state when its index is absent from the source event schedule. Errors are included. -/
theorem normal_unvisited (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor query : UniIndex) (node : TreeNode) (kind : AccessKind) (mode : ChildrenVisitMode)
    (present : tree.nodeAt query = some node)
    (outside : ∀ event ∈ ((source_normal_projection tree location protections).topology.traverse
        anchor.toNat mode (sourceNormalSkipped (source_normal_projection tree location protections) kind)).2,
      event.node ≠ query.toNat) :
    (tree.performNormalAccessAt location anchor kind protections mode).location.perms.get query = location.perms.get query := by
  have unvisited := events_unvisited
    ((source_normal_projection tree location protections).topology.traverse anchor.toNat mode
      (sourceNormalSkipped (source_normal_projection tree location protections) kind)).2
    ((source_normal_projection tree location protections).topology.traverse anchor.toNat mode
      (sourceNormalSkipped (source_normal_projection tree location protections) kind)).1
    kind (source_normal_projection tree location protections) query.toNat outside
  have projected : (source_normal_projection tree location protections).locationStates[query.toNat]? =
      some (location.perms.get query) := by
    unfold_general_projection
    rw [Array.getElem?_mapIdx]
    obtain ⟨valid,stored⟩ := array_of_node tree query node present
    simp only [Array.getElem?_eq_getElem valid,stored,Option.map_some,index_self]
  change ((source_normal_projection tree location protections).performAccess anchor.toNat kind mode).tree.locationStates[query.toNat]? =
      (source_normal_projection tree location protections).locationStates[query.toNat]? at unvisited
  rw [projected] at unvisited
  rw [source_normal_perms]
  unfold_clean_write_states
  simp only [Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  change (forIn _ location (source_write_scan _)).perms.get query = location.perms.get query
  rw [source_write_list_get]
  split
  · rw [unvisited]
    cases location.perms.get query <;> rfl
  · rfl

/-- An arbitrary normal component followed by an exposed mutable first-root
leaf completes the real two-root access loop. The foreign root is position zero,
so the actual call uses isWildcardTree=false. All success facts are derived
from initial ownership, event-local exposure flags and raw leaf/cache data. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor normalRoot foreignRoot : UniIndex) (anchorNode normalNode foreignNode : TreeNode)
    (kind : AccessKind) (range : ByteRange)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location protections) anchor.toNat kind)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (normalPresent : tree.nodes.get normalRoot = some normalNode)
    (roots : tree.roots = #[foreignRoot,normalRoot]) (different : normalRoot ≠ foreignRoot)
    (rootPath : ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast! = normalRoot.toNat)
    (foreign : GeneralBorrowWildcardLeaf.Data tree location foreignRoot foreignNode normalNode.tag)
    (unexposed : ∀ event ∈ ((source_normal_projection tree location protections).performAccess
        anchor.toNat kind .VisitChildrenOfAccessed).visited, ∀ index node,
      UniIndex.ofNat? event.node = some index → tree.nodeAt index = some node → node.isExposed = false) :
    source_access_location (source_tree_access_at tree location (some anchor) kind protections .VisitChildrenOfAccessed range) =
      (tree.performNormalAccessAt location anchor kind protections .VisitChildrenOfAccessed).location ∧
    source_access_status (source_tree_access_at tree location (some anchor) kind protections .VisitChildrenOfAccessed range) = none := by
  have normalGood := GeneralBorrowNormalLocation.normal_succeeds tree location protections anchor kind
    .VisitChildrenOfAccessed forest owned depth children anchorNode anchorPresent
  have normalRootEq : (tree.performNormalAccessAt location anchor kind protections .VisitChildrenOfAccessed).access.root = normalRoot.toNat :=
    (GeneralBorrowStorage.events_root _ _ kind (source_normal_projection tree location protections)).trans rootPath
  have converted : UniIndex.ofNat? (tree.performNormalAccessAt location anchor kind protections .VisitChildrenOfAccessed).access.root = some normalRoot := by
    rw [normalRootEq];exact index_self normalRoot
  have visited := GeneralBorrowStorage.events_visited
    ((source_normal_projection tree location protections).topology.traverse anchor.toNat .VisitChildrenOfAccessed
      (sourceNormalSkipped (source_normal_projection tree location protections) kind)).2
    ((source_normal_projection tree location protections).topology.traverse anchor.toNat .VisitChildrenOfAccessed
      (sourceNormalSkipped (source_normal_projection tree location protections) kind)).1
    kind (source_normal_projection tree location protections) normalGood.1
  change ((source_normal_projection tree location protections).performAccess anchor.toNat kind .VisitChildrenOfAccessed).visited =
    ((source_normal_projection tree location protections).topology.traverse anchor.toNat .VisitChildrenOfAccessed
      (sourceNormalSkipped (source_normal_projection tree location protections) kind)).2 at visited
  have outside : ∀ event ∈ ((source_normal_projection tree location protections).topology.traverse anchor.toNat
        .VisitChildrenOfAccessed (sourceNormalSkipped (source_normal_projection tree location protections) kind)).2,
      event.node ≠ foreignRoot.toNat := by
    intro event member same
    have actualMember : event ∈ ((source_normal_projection tree location protections).performAccess anchor.toNat kind .VisitChildrenOfAccessed).visited := by
      rw [visited];exact member
    have conversion : UniIndex.ofNat? event.node = some foreignRoot := by rw [same];exact index_self foreignRoot
    have flag := unexposed event actualMember foreignRoot foreignNode conversion foreign.present
    rw [foreign.exposed] at flag
    cases flag
  have foreignStored := normal_unvisited tree location protections anchor foreignRoot foreignNode kind
    .VisitChildrenOfAccessed foreign.present outside
  have cache := GeneralBorrowNormalEventCacheFrame.normal_cache tree location anchor kind protections
    .VisitChildrenOfAccessed unexposed
  have afterData : GeneralBorrowWildcardLeaf.Data tree
      (tree.performNormalAccessAt location anchor kind protections .VisitChildrenOfAccessed).location foreignRoot foreignNode normalNode.tag :=
    ⟨foreign.present,foreign.leaf,foreign.exposed,foreignStored.trans foreign.writable,
      by rw [cache];exact foreign.cache,foreign.boundedTag⟩
  have wildcard := GeneralBorrowWildcardLeaf.access tree _ foreignRoot foreignNode normalNode.tag kind protections afterData
  simp_tree_helpers
  simp only [normalGood.1,normalGood.2,normalRootEq,index_self]
  simp only [roots,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    show #[foreignRoot,normalRoot].size = 2 from rfl,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one,
    show List.range' 0 2 = [0,1] from rfl]
  simp [List.forIn_cons,List.forIn_nil,wildcard,bind,pure,normalPresent,different]
end DuplicatePrefix.GeneralBorrowTwoRootNormalAccess
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowTwoRootNormalAccess." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual two-root normal access dependency {dependency}"
