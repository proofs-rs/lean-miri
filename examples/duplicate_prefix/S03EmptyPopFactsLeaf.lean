import duplicate_prefix.S03EmptyPopFactsForeign
import duplicate_prefix.GeneralBorrowPhysicalRootPath
import duplicate_prefix.GeneralBorrowProtectedReadPermissionMetadata

namespace DuplicatePrefix.S03EmptyPopFactsLeaf
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForest GeneralBorrowTopology GeneralBorrowProjection BorrowRangeAccess
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

theorem leaf_desc (tree : TraversalTree) (forest : Forest tree)
    (leaf : Nat) (valid : leaf < tree.nodes.size) (empty : tree.nodes[leaf].children = [])
    (other : Nat) (path : Desc tree leaf other) : leaf = other := by
  induction path with
  | refl => rfl
  | @step parent child earlier bounded edge ih =>
    have member := (forest.parentChild child bounded parent edge).2
    subst parent
    rw [empty] at member
    simp at member

/-- A fresh empty child is a leaf before body reborrows. Any distinct normal
access therefore sees it only as foreign, irrespective of the selected root. -/
theorem foreign_events (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (query source : UniIndex) (node sourceNode : TreeNode)
    (present : tree.nodeAt query = some node) (sourcePresent : tree.nodeAt source = some sourceNode)
    (leaf : node.children = #[]) (different : query ≠ source)
    (forest : Forest (source_normal_projection tree location protections).topology)
    (kind : AccessKind) (mode : ChildrenVisitMode) :
    ∀ event ∈ ((source_normal_projection tree location protections).topology.traverse source.toNat mode
      (sourceNormalSkipped (source_normal_projection tree location protections) kind)).2,
      event.node = query.toNat → event.relatedness = .ForeignAccess := by
  let normal := source_normal_projection tree location protections
  have valid := GeneralBorrowProtectedReadPermissionMetadata.valid_anchor tree location protections source sourceNode sourcePresent
  have queryValid := GeneralBorrowProtectedReadPermissionMetadata.valid_anchor tree location protections query node present
  have empty : normal.topology.nodes[query.toNat].children = [] := by
    have projected := projection_topology_node tree location protections query.toNat query node rfl present
    simp only [Array.getElem?_eq_getElem queryValid,Option.getD_some] at projected
    rw [projected,leaf]
    rfl
  have outside : query.toNat ∉ normal.topology.ancestorPath source.toNat := by
    intro member
    have path := GeneralBorrowPhysicalRootPath.ancestor_desc normal.topology forest _ source.toNat query.toNat valid member
    have equal := leaf_desc normal.topology forest query.toNat queryValid empty source.toNat path
    exact different (GeneralBorrowNodeUpdate.index_injective query source equal)
  intro event member equal
  have scheduled := (GeneralBorrowTraversal.traversal_data normal.topology forest source.toNat valid mode
    (sourceNormalSkipped normal kind)).2 event member
  rw [scheduled.2,equal,if_neg outside]

/-- The actual normal part of the return Write retains the empty leaf's
inactive bit, including states materialized by that Write. No normal-access
completion or post-state permission is supplied. -/
theorem normal (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (query source : UniIndex) (node sourceNode : TreeNode)
    (present : tree.nodeAt query = some node) (sourcePresent : tree.nodeAt source = some sourceNode)
    (leaf : node.children = #[]) (different : query ≠ source)
    (forest : Forest (source_normal_projection tree location protections).topology)
    (kind : AccessKind) (mode : ChildrenVisitMode)
    (inactive : S03EmptyPopFactsForeign.LocationTyped location query) :
    S03EmptyPopFactsForeign.LocationTyped (tree.performNormalAccessAt location source kind protections mode).location query :=
  S03EmptyPopFactsForeign.normal tree location protections source query kind mode inactive
    (foreign_events tree location protections query source node sourceNode present sourcePresent leaf different forest kind mode)

end DuplicatePrefix.S03EmptyPopFactsLeaf
