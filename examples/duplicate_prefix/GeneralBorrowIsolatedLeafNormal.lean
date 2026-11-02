import duplicate_prefix.GeneralBorrowParentlessTraversal
import duplicate_prefix.GeneralBorrowTwoRootNormalAccess
import duplicate_prefix.GeneralBorrowExposedVirtualSchedule
namespace DuplicatePrefix.GeneralBorrowIsolatedLeafNormal
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open DuplicatePrefix.GeneralBorrowFrontier DuplicatePrefix.GeneralBorrowEvents
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

theorem schedule (tree : TraversalTree) (anchor : Nat) (mode : ChildrenVisitMode) (skips : List Nat)
    (valid : anchor < tree.nodes.size) (parentless : tree.nodes[anchor].parent = none)
    (leaf : tree.nodes[anchor].children = []) :
    tree.traverse anchor mode skips = (anchor,[⟨anchor,.LocalAccess⟩]) := by
  have path := GeneralBorrowParentlessTraversal.ancestor_path tree anchor valid parentless
  have foreign : sourceForeignRoots tree [anchor] mode = [] := by
    change sourceForeignRootsGo tree mode [anchor] none true = []
    rw [roots_cons,roots_nil]
    simp only [deferredHeads,Array.getElem?_eq_getElem valid,Option.getD_some,leaf,List.reverse_nil,List.filter_nil,List.append_nil]
    split <;> rfl
  simp only [TraversalTree.traverse,path,foreign,List.map_cons,List.map_nil,List.flatMap_nil,List.append_nil]
  rfl

/-- A physical isolated root needs ownership only of its actual local event.
Other components may hold active protected Unique nodes: no ForeignOwned
condition is imposed on nodes the normal traversal cannot visit. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (node : TreeNode) (kind : AccessKind) (mode : ChildrenVisitMode)
    (present : tree.nodeAt anchor = some node) (parentless : node.parent = none) (leaf : node.children = #[])
    (hidden : node.isExposed = false) (state : LocationState)
    (stored : location.perms.get anchor = some state)
    (owned : ∀ held, GeneralBorrowPermissions.AccessOwned state kind .LocalAccess held) :
    (tree.performNormalAccessAt location anchor kind protections mode).access.status = .Completed ∧
    (tree.performNormalAccessAt location anchor kind protections mode).outcome = .ok () ∧
    (tree.performNormalAccessAt location anchor kind protections mode).access.root = anchor.toNat ∧
    (tree.performNormalAccessAt location anchor kind protections mode).location.exposedCache = location.exposedCache ∧
    (∀ query next, tree.nodeAt query = some next → query ≠ anchor →
      (tree.performNormalAccessAt location anchor kind protections mode).location.perms.get query = location.perms.get query) := by
  let projection := source_normal_projection tree location protections
  have sizes := projection_sizes tree location protections
  have valid : anchor.toNat < projection.topology.nodes.size := by
    have bounded := GeneralBorrowNodeUpdate.lookup_valid tree.nodes anchor node present
    dsimp only [projection]
    unfold_general_projection;unfold_general_topology
    simpa only [Array.size_map] using bounded
  have projected := projection_topology_node tree location protections anchor.toNat anchor node rfl present
  have shape : projection.topology.nodes[anchor.toNat] = ⟨none,[]⟩ := by
    rw [Array.getElem?_eq_getElem valid,Option.getD_some,parentless,leaf] at projected
    exact projected
  have events := schedule projection.topology anchor.toNat mode (sourceNormalSkipped projection kind) valid
    (by rw [shape]) (by rw [shape])
  have statePresent : projection.stateAt anchor.toNat = some state := by
    rw [projection_state tree location protections anchor.toNat anchor node (index_self anchor) rfl present]
    simp [stored]
  have stateValid : anchor.toNat < projection.locationStates.size := by
    dsimp only [projection]
    rw [sizes.1]
    exact GeneralBorrowNodeUpdate.lookup_valid tree.nodes anchor node present
  have completed : (projection.performAccess anchor.toNat kind mode).status = .Completed := by
    apply normal_access_complete
    · rw [events];simp
    · rw [events]
      intro event member
      have same : event = ⟨anchor.toNat,.LocalAccess⟩ := List.mem_singleton.mp member
      subst event
      exact ⟨state,statePresent,stateValid,owned _,Or.inl rfl⟩
  have visited := GeneralBorrowStorage.events_visited _ _ kind projection completed
  change (projection.performAccess anchor.toNat kind mode).visited =
    (projection.topology.traverse anchor.toNat mode (sourceNormalSkipped projection kind)).2 at visited
  rw [events] at visited
  have rootEq : (projection.performAccess anchor.toNat kind mode).root = anchor.toNat := by
    have root := GeneralBorrowStorage.events_root
      (projection.topology.traverse anchor.toNat mode (sourceNormalSkipped projection kind)).2
      (projection.topology.traverse anchor.toNat mode (sourceNormalSkipped projection kind)).1 kind projection
    change (projection.performAccess anchor.toNat kind mode).root =
      (projection.topology.traverse anchor.toNat mode (sourceNormalSkipped projection kind)).1 at root
    rw [events] at root
    exact root
  have outcome : (tree.performNormalAccessAt location anchor kind protections mode).outcome = .ok () := by
    unfold BorrowTree.performNormalAccessAt
    simp only [Id.run,bind,pure,ForIn.forIn]
    dsimp only [projection] at visited
    rw [visited]
    simp only [List.forIn'_cons,List.forIn'_nil,index_self,present,hidden,Bool.false_and,Bool.false_eq_true,↓reduceIte,bind,pure]
  have unexposed : ∀ event ∈ (projection.performAccess anchor.toNat kind mode).visited, ∀ index next,
      UniIndex.ofNat? event.node = some index → tree.nodeAt index = some next → next.isExposed = false := by
    intro event member index next converted found
    rw [visited] at member
    have same := List.mem_singleton.mp member
    subst event
    rw [index_self] at converted
    cases converted
    have equal := Option.some.inj (present.symm.trans found)
    subst next
    exact hidden
  refine ⟨completed,outcome,rootEq,GeneralBorrowNormalEventCacheFrame.normal_cache tree location anchor kind protections mode unexposed,?_⟩
  intro query next found different
  apply GeneralBorrowTwoRootNormalAccess.normal_unvisited tree location protections anchor query next kind mode found
  intro event member
  rw [events] at member
  have same := List.mem_singleton.mp member
  subst event
  exact fun equal => different (GeneralBorrowNodeUpdate.index_injective query anchor equal.symm)

/-- The actual isolated unexposed local call retains coherent exposure counts,
without conditions on exposed permissions in other physical components. -/
theorem coherent (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (node : TreeNode) (kind : AccessKind) (mode : ChildrenVisitMode)
    (present : tree.nodeAt anchor = some node) (parentless : node.parent = none) (leaf : node.children = #[])
    (hidden : node.isExposed = false) (state : LocationState) (stored : location.perms.get anchor = some state)
    (owned : ∀ held, GeneralBorrowPermissions.AccessOwned state kind .LocalAccess held)
    (initial : GeneralBorrowExposureCardinality.LocationCoherent tree location protections) :
    GeneralBorrowExposureCardinality.LocationCoherent tree
      (tree.performNormalAccessAt location anchor kind protections mode).location protections := by
  have good := access tree location protections anchor node kind mode present parentless leaf hidden state stored owned
  intro query accessKind
  rw [good.2.2.2.1,initial query accessKind]
  unfold GeneralBorrowExposureCardinality.cardinality
  apply congrArg UInt16.ofNat
  apply congrArg List.length
  apply List.filter_congr
  intro row member
  have found := (GeneralBorrowFreshReuseProtection.entries_get tree.nodes row.1 row.2).mp member
  by_cases same : row.1 = anchor
  · have equal : row.2 = node := Option.some.inj ((same ▸ found).symm.trans present)
    simp only [GeneralBorrowExposureCardinality.contributes,equal,hidden,Bool.false_and]
  · simp only [GeneralBorrowExposureCardinality.contributes,GeneralBorrowExposureCardinality.effective,
      good.2.2.2.2 row.1 row.2 found same]

end DuplicatePrefix.GeneralBorrowIsolatedLeafNormal
