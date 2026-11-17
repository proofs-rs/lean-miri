import duplicate_prefix.GeneralBorrowFreshReuseProjection
import duplicate_prefix.GeneralBorrowFreshMaterialization
namespace DuplicatePrefix.GeneralBorrowFreshReuseState
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowFreshNode
open DuplicatePrefix.GeneralBorrowNodeUpdate DuplicatePrefix.GeneralBorrowFreshMaterialization
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
private def absentDefault : LocationState := ⟨.Disabled,false,.None⟩

private theorem projection_slot (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (position : Nat) (query : UniIndex) (converted : UniIndex.ofNat? position = some query)
    (equal : query.toNat = position) (valid : position < tree.nodes.data.size) :
    (source_normal_projection tree location protections).stateAt position =
      some ((location.perms.get query).getD (((tree.nodeAt query).map TreeNode.defaultLocationState).getD absentDefault)) := by
  have nodeValue : tree.nodeAt query = tree.nodes.data[position]'valid := by
    unfold BorrowTree.nodeAt UniValMap.get
    simp only [equal,Array.getElem?_eq_getElem valid]
  unfold_general_projection
  unfold NormalTreeState.stateAt
  simp only [Array.getElem?_mapIdx,Array.getElem?_map,Array.getElem?_eq_getElem valid,
    converted,Option.map_some]
  rw [nodeValue]
  generalize stateEq : location.perms.get query = stored
  clear stateEq
  generalize nodeEq : tree.nodes.data[position] = node
  clear nodeEq
  cases stored <;> cases node <;> rfl


/-- Reusing a bounded vacant slot keeps the actual node-table length. -/
theorem attached_size (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (valid : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (parentPresent : tree.nodeAt parent = some parentNode) :
    (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode).nodes.data.size = tree.nodes.data.size := by
  have old := (GeneralBorrowFreshLocation.get_other tree.nodes index parent newNode
    (GeneralBorrowFreshReuseNode.parent_not_vacant tree.nodes index parent parentNode vacant parentPresent)).trans parentPresent
  change ((tree.nodes.insert index newNode).insert parent {parentNode with children := parentNode.children.push index}).size = tree.nodes.size
  rw [insert_existing_size (tree.nodes.insert index newNode) parent parentNode _ old,
    GeneralBorrowFreshReuseNode.bounded_size tree.nodes index newNode valid]

private theorem old_default (tree : BorrowTree) (index parent query : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode)
    (different : query ≠ index) :
    (((GeneralBorrowFreshGraph.attached tree index parent parentNode newNode).nodeAt query).map TreeNode.defaultLocationState).getD absentDefault =
      ((tree.nodeAt query).map TreeNode.defaultLocationState).getD absentDefault := by
  have old := (GeneralBorrowFreshLocation.get_other tree.nodes index parent newNode
    (GeneralBorrowFreshReuseNode.parent_not_vacant tree.nodes index parent parentNode vacant parentPresent)).trans parentPresent
  change tree.nodes.get parent = some parentNode at parentPresent
  dsimp only [GeneralBorrowFreshGraph.attached,attachedNodes,BorrowTree.nodeAt]
  by_cases same : query = parent
  · subst query
    rw [insert_existing_get_same (tree.nodes.insert index newNode) parent parentNode _ old,parentPresent]
    rfl
  · rw [insert_existing_get_other (tree.nodes.insert index newNode) parent query parentNode _ old same,
      GeneralBorrowFreshLocation.get_other tree.nodes index query newNode different]

/-- Every position other than the reused slot retains its exact effective
state when the new child's inside permission is materialized. The explicit
u32 node-table bound also covers sparse/missing node slots. -/
theorem state_old (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (bounded : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (parentPresent : tree.nodeAt parent = some parentNode) (fits : tree.nodes.data.size ≤ 4294967296)
    (location : LocationTree) (state : LocationState) (protections : ProtectedTags)
    (position : Nat) (valid : position < tree.nodes.data.size) (different : position ≠ index.toNat) :
    (source_normal_projection (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode)
      (materialized location index state) protections).stateAt position =
      (source_normal_projection tree location protections).stateAt position := by
  obtain ⟨query,converted,equal⟩ := index_nat position (by omega)
  have queryDifferent : query ≠ index := by intro same;exact different (equal.symm.trans (congrArg UniIndex.toNat same))
  have validAfter : position < (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode).nodes.data.size := by
    rw [attached_size tree index parent parentNode newNode bounded vacant parentPresent]
    exact valid
  rw [projection_slot _ _ _ position query converted equal validAfter,
    projection_slot tree location protections position query converted equal valid]
  dsimp only [materialized]
  rw [GeneralBorrowFreshLocation.get_other location.perms index query state queryDifferent,
    old_default tree index parent query parentNode newNode vacant parentPresent queryDifferent]

/-- The reused slot is overwritten with the actual new child state, regardless
of any stale per-location state that may have remained at that slot. -/
theorem state_new (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (bounded : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (parentPresent : tree.nodeAt parent = some parentNode)
    (location : LocationTree) (state : LocationState) (protections : ProtectedTags) :
    (source_normal_projection (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode)
      (materialized location index state) protections).stateAt index.toNat = some state := by
  have valid : index.toNat < (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode).nodes.data.size := by
    rw [attached_size tree index parent parentNode newNode bounded vacant parentPresent]
    exact bounded
  rw [projection_slot _ _ _ index.toNat index (index_self index) rfl valid]
  dsimp only [materialized]
  rw [GeneralBorrowFreshLocation.get_same]
  rfl
end DuplicatePrefix.GeneralBorrowFreshReuseState
#print axioms DuplicatePrefix.GeneralBorrowFreshReuseState.state_old
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshReuseState." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved reused state dependency {dependency}"
