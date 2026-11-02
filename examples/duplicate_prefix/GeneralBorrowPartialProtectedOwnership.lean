import duplicate_prefix.GeneralBorrowFreshChild
import duplicate_prefix.GeneralBorrowPartitionState
import duplicate_prefix.GeneralBorrowFreshModify
import duplicate_prefix.GeneralBorrowFreshOwnership

namespace DuplicatePrefix.GeneralBorrowPartialProtectedOwnership
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.BorrowRangeAccess
open DuplicatePrefix.GeneralBorrowFreshGraph DuplicatePrefix.GeneralBorrowFreshMaterialization DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem slot (tree : BorrowTree) (location : LocationTree) (position : Nat) (query : UniIndex)
    (converted : UniIndex.ofNat? position = some query) (equal : query.toNat = position)
    (valid : position < tree.nodes.data.size) :
    (source_normal_projection tree location {}).stateAt position =
      some ((location.perms.get query).getD
        (((tree.nodeAt query).map TreeNode.defaultLocationState).getD ⟨.Disabled,false,.None⟩)) := by
  have nodeValue : tree.nodeAt query = tree.nodes.data[position]'valid := by
    unfold BorrowTree.nodeAt UniValMap.get
    simp only [equal,Array.getElem?_eq_getElem valid]
  unfold_general_projection
  unfold NormalTreeState.stateAt
  simp only [Array.getElem?_mapIdx,Array.getElem?_map,Array.getElem?_eq_getElem valid,converted,Option.map_some]
  rw [nodeValue]
  cases stored : location.perms.get query <;> cases tree.nodes.data[position] <;> rfl

private theorem path (tree : BorrowTree) (root : UniIndex) (node : TreeNode) (location : LocationTree)
    (present : tree.nodeAt root = some node) (parentless : node.parent = none) :
    (source_normal_projection tree location {}).topology.ancestorPath root.toNat = [root.toNat] := by
  have parent : (DuplicatePrefix.GeneralBorrowPresence.nodeData (source_normal_projection tree location {}).topology root.toNat).parent = none := by
    change ((source_normal_projection tree location {}).topology.nodes[root.toNat]?.getD ⟨none,[]⟩).parent = none
    rw [projection_topology_node tree location {} root.toNat root node rfl present]
    simp only [parentless,Option.map_none]
  change sourceAncestorPath (source_normal_projection tree location {}).topology
    (source_normal_projection tree location {}).topology.nodes.size root.toNat = _
  cases (source_normal_projection tree location {}).topology.nodes.size with
  | zero => rfl
  | succ fuel => rw [GeneralBorrowPresence.ancestor_succ,parent]

private theorem unheld (tree : BorrowTree) (location : LocationTree) (position : Nat) :
    (source_normal_projection tree location {}).protectedNodes.contains position = false := by
  have empty : (source_normal_projection tree location {}).protectedNodes = [] := by
    unfold_general_projection
    simp [ProtectedTags.contains,ProtectedTags.get]
  rw [empty];rfl

private theorem defaults (tree : BorrowTree) (index root query : UniIndex) (node leaf : TreeNode)
    (different : query ≠ index) (notRoot : root ≠ index) (present : tree.nodeAt root = some node) :
    (((attached tree index root node leaf).nodeAt query).map TreeNode.defaultLocationState).getD ⟨.Disabled,false,.None⟩ =
      ((tree.nodeAt query).map TreeNode.defaultLocationState).getD ⟨.Disabled,false,.None⟩ := by
  have parentBefore : tree.nodes.get root = some node := present
  have parentAfter : (tree.nodes.insert index leaf).get root = some node :=
    (GeneralBorrowFreshLocation.get_other tree.nodes index root leaf notRoot).trans parentBefore
  change (((((tree.nodes.insert index leaf).insert root (updatedParent node index)).get query)).map TreeNode.defaultLocationState).getD _ = _
  by_cases same : query = root
  · subst query
    rw [GeneralBorrowFreshLocation.get_same,present]
    rfl
  · rw [GeneralBorrowFreshLocation.get_other _ root query _ same,GeneralBorrowFreshLocation.get_other tree.nodes index query leaf different]
    rfl

/-- Installing an counterfactual unheld mutable reservation preserves the root's Write ownership
both inside the selected range and outside it. Outside, its real lazy default is
ReservedFrz(false), rather than an invented absent node or successful no-op. -/
theorem location (tree : BorrowTree) (root index : UniIndex) (node : TreeNode) (tag : BorTag)
    (present : tree.nodeAt root = some node) (parentless : node.parent = none) (notRoot : root ≠ index)
    (rootAfter : (attached tree index root node (GeneralBorrowFreshChild.child tag root)).nodeAt root = some (updatedParent node index))
    (leafAfter : (attached tree index root node (GeneralBorrowFreshChild.child tag root)).nodeAt index = some (GeneralBorrowFreshChild.child tag root))
    (fits : (attached tree index root node (GeneralBorrowFreshChild.child tag root)).nodes.data.size ≤ 4294967296)
    (oldPosition : ∀ position, position < (attached tree index root node (GeneralBorrowFreshChild.child tag root)).nodes.data.size →
      position ≠ index.toNat → position < tree.nodes.data.size)
    (before after : LocationTree)
    (same : ∀ query, query ≠ index → after.perms.get query = before.perms.get query)
    (inserted : after.perms.get index = none ∨ after.perms.get index = some GeneralBorrowFreshChild.inside)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree before {}) root.toNat .Write) :
    GeneralBorrowAnchor.AnchorOwned
      (source_normal_projection (attached tree index root node (GeneralBorrowFreshChild.child tag root)) after {}) root.toNat .Write := by
  let next := attached tree index root node (GeneralBorrowFreshChild.child tag root)
  have topologySize : (source_normal_projection next after {}).topology.nodes.size = next.nodes.data.size := by
    unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
  have fitNext : next.nodes.data.size ≤ 4294967296 := fits
  have oldSize : (source_normal_projection tree before {}).topology.nodes.size = tree.nodes.data.size := by
    unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
  have rootPath := path next root (updatedParent node index) after rootAfter parentless
  have oldPath := path tree root node before present parentless
  refine ⟨?_,(projection_sizes next after {}).1.trans topologySize.symm,
    (projection_sizes next after {}).2.trans topologySize.symm,?_⟩
  · rw [topologySize]
    exact GeneralBorrowNodeUpdate.lookup_valid next.nodes root _ rootAfter
  · intro position valid
    have bound : position < next.nodes.data.size := by rw [←topologySize];exact valid
    obtain ⟨query,converted,equal⟩ := index_nat position (by omega)
    by_cases isNew : query = index
    · subst query
      have different : position ≠ root.toNat := by
        intro eq
        exact notRoot (GeneralBorrowNodeUpdate.index_injective root index (eq.symm.trans equal.symm))
      rw [slot next after position index converted equal bound,leafAfter]
      rw [GeneralBorrowAnchor.relation,rootPath]
      simp only [List.mem_singleton,ite_eq_right different,unheld]
      rcases inserted with absent | stored
      · refine ⟨(GeneralBorrowFreshChild.child tag root).defaultLocationState,?_,?_⟩
        · simp only [absent,Option.getD_none,Option.map_some,Option.getD_some]
        · exact ⟨rfl,Or.inl rfl⟩
      · refine ⟨GeneralBorrowFreshChild.inside,?_,?_⟩
        · simp only [stored,Option.getD_some]
        · exact ⟨rfl,Or.inl rfl⟩
    · have different : position ≠ index.toNat := by
        intro eq
        exact isNew (GeneralBorrowNodeUpdate.index_injective query index (equal.trans eq))
      have oldBound := oldPosition position bound different
      obtain ⟨state,stored,permission⟩ := owned.permissions position (by rw [oldSize];exact oldBound)
      refine ⟨state,?_,?_⟩
      · rw [slot next after position query converted equal bound,same query isNew,defaults tree index root query node _ isNew notRoot present,
          ←slot tree before position query converted equal oldBound]
        exact stored
      · simpa only [next,GeneralBorrowAnchor.relation,show (source_normal_projection (attached tree index root node (GeneralBorrowFreshChild.child tag root)) after {}).topology.ancestorPath root.toNat = [root.toNat] from rootPath,oldPath,unheld] using permission

end DuplicatePrefix.GeneralBorrowPartialProtectedOwnership
