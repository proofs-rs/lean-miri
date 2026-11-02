import duplicate_prefix.S02ConstructorNormalTopology
import duplicate_prefix.S02ConstructorSupportTopology
import duplicate_prefix.GeneralBorrowFreshReuseProtection
import duplicate_prefix.GeneralBorrowFreshSharedPaths

namespace DuplicatePrefix.S02ConstructorOutsideProjection
open Miri Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowFreshNode GeneralBorrowFreshGraph GeneralBorrowPresence
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
attribute [local irreducible] UniValMap.insert

def absentDefault : LocationState := ⟨.Disabled,false,.None⟩

/-- Natural-position projection includes sparse/vacant old slots. -/
theorem projection_slot (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (position : Nat) (query : UniIndex) (converted : UniIndex.ofNat? position = some query)
    (equal : query.toNat = position) (valid : position < tree.nodes.data.size) :
    (source_normal_projection tree location protections).stateAt position =
      some ((location.perms.get query).getD (((tree.nodeAt query).map TreeNode.defaultLocationState).getD absentDefault)) := by
  have nodeValue : tree.nodeAt query = tree.nodes.data[position]'valid := by
    unfold BorrowTree.nodeAt UniValMap.get
    simp only [equal,Array.getElem?_eq_getElem valid]
  unfold_general_projection
  unfold NormalTreeState.stateAt
  simp only [Array.getElem?_mapIdx,Array.getElem?_map,Array.getElem?_eq_getElem valid,converted,Option.map_some]
  rw [nodeValue]
  generalize stateEq : location.perms.get query = stored
  generalize nodeEq : tree.nodes.data[position] = node
  cases stored <;> cases node <;> rfl

/-- Old default scalar states survive physical attachment, even at vacant slots. -/
theorem old_default (tree : BorrowTree) (index parent query : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode)
    (different : query ≠ index) :
    (((attached tree index parent parentNode newNode).nodeAt query).map TreeNode.defaultLocationState).getD absentDefault =
      ((tree.nodeAt query).map TreeNode.defaultLocationState).getD absentDefault := by
  by_cases same : query = parent
  · subst query
    rw [GeneralBorrowFreshMetadataChildReuseGraph.parent_lookup tree index parent parentNode newNode vacant parentPresent,parentPresent]
    rfl
  · rw [GeneralBorrowFreshMetadataChildReuseGraph.other_lookup tree index parent query parentNode newNode vacant parentPresent same different]

/-- Outside materialization, old projected scalar states remain exact. -/
theorem state_old (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode)
    (fits : tree.nodes.data.size ≤ 4294967296) (location : LocationTree) (protections : ProtectedTags)
    (position : Nat) (valid : position < tree.nodes.data.size)
    (validAfter : position < (attached tree index parent parentNode newNode).nodes.data.size)
    (different : position ≠ index.toNat) :
    (source_normal_projection (attached tree index parent parentNode newNode) location protections).stateAt position =
      (source_normal_projection tree location protections).stateAt position := by
  obtain ⟨query,converted,equal⟩ := index_nat position (by omega)
  have neq : query ≠ index := by intro same;exact different (equal.symm.trans (congrArg UniIndex.toNat same))
  rw [projection_slot _ _ _ position query converted equal validAfter,
    projection_slot _ _ _ position query converted equal valid,
    old_default tree index parent query parentNode newNode vacant parentPresent neq]

/-- The physical mutable child's untouched outside row has its lazy default. -/
theorem state_new (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode)
    (location : LocationTree) (protections : ProtectedTags) (clean : location.perms.get index = none) :
    (source_normal_projection (attached tree index parent parentNode (GeneralBorrowFreshChild.child tag parent))
      location protections).stateAt index.toNat = some ⟨.ReservedFrz false,false,.None⟩ := by
  rw [projection_state _ _ _ index.toNat index _ (index_self index) rfl
    (GeneralBorrowFreshMetadataChildReuseGraph.new_lookup tree index parent parentNode _ vacant parentPresent),clean]
  rfl

/-- Data-only projection consequences needed for an arbitrary destination's
full normal table. The fresh protector bit is unrestricted. -/
structure Extension (before after : NormalTreeState) (parent child : Nat) : Prop where
  paths : GeneralBorrowFreshSharedPaths.Attach before.topology after.topology parent child
  oldValid : ∀ position,position < after.topology.nodes.size → position ≠ child → position < before.topology.nodes.size
  oldState : ∀ position,position < before.topology.nodes.size → position ≠ child → after.stateAt position = before.stateAt position
  newState : after.stateAt child = some ⟨.ReservedFrz false,false,.None⟩
  oldProtected : ∀ position,position < before.topology.nodes.size → position ≠ child →
    after.protectedNodes.contains position = before.protectedNodes.contains position

 theorem topology_size (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) :
    (source_normal_projection tree location protections).topology.nodes.size = tree.nodes.data.size := by
  unfold_general_projection
  unfold_general_topology
  simp only [Array.size_map]

/-- Append creates the exact untouched destination-row projection extension. -/
theorem append_extension (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (atEnd : index.toNat = tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (present : tree.nodeAt parent = some parentNode) (fits : tree.nodes.data.size ≤ 4294967296)
    (location : LocationTree) (protections : ProtectedTags) (clean : location.perms.get index = none)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology) :
    Extension (source_normal_projection tree location protections)
      (source_normal_projection (attached tree index parent parentNode (GeneralBorrowFreshChild.child tag parent))
        location protections) parent.toNat index.toNat := by
  have ext := GeneralBorrowFreshProjection.topology_extension tree index parent parentNode (GeneralBorrowFreshChild.child tag parent) atEnd present rfl rfl location location protections
  have size := topology_size tree location protections
  have afterSize := topology_size (attached tree index parent parentNode (GeneralBorrowFreshChild.child tag parent)) location protections
  have indexEq : index.toNat = (source_normal_projection tree location protections).topology.nodes.size := atEnd.trans size.symm
  have paths := GeneralBorrowFreshSharedPaths.of_append _ _ parent.toNat ext forest
  rw [←indexEq] at paths
  refine ⟨paths,?_,?_,state_new tree index parent parentNode tag vacant present location protections clean,?_⟩
  · intro position valid different
    rw [ext.length] at valid
    rw [indexEq] at different
    omega
  · intro position valid different
    apply state_old tree index parent parentNode _ vacant present fits location protections position (by omega) _ different
    rw [←afterSize,ext.length]
    omega
  · intro position valid different
    exact GeneralBorrowFreshReuseProtection.protection_position tree index parent parentNode _ vacant present location location
      protections fits position (by omega) different

/-- Bounded reuse creates the same exact projection extension and preserves
sparse old state/protector rows. -/
theorem reuse_extension (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (bounded : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (present : tree.nodeAt parent = some parentNode) (fits : tree.nodes.data.size ≤ 4294967296)
    (location : LocationTree) (protections : ProtectedTags) (clean : location.perms.get index = none)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology) :
    Extension (source_normal_projection tree location protections)
      (source_normal_projection (attached tree index parent parentNode (GeneralBorrowFreshChild.child tag parent))
        location protections) parent.toNat index.toNat := by
  have ext := GeneralBorrowFreshReuseProjection.topology_extension tree index parent parentNode (GeneralBorrowFreshChild.child tag parent) bounded vacant present rfl rfl location location protections
  have size := topology_size tree location protections
  have afterSize := topology_size (attached tree index parent parentNode (GeneralBorrowFreshChild.child tag parent)) location protections
  refine ⟨GeneralBorrowFreshSharedPaths.of_reuse _ _ index.toNat parent.toNat ext forest,?_,?_,
    state_new tree index parent parentNode tag vacant present location protections clean,?_⟩
  · intro position valid different
    rw [ext.length] at valid
    exact valid
  · intro position valid different
    apply state_old tree index parent parentNode _ vacant present fits location protections position (by omega) _ different
    rw [←afterSize,ext.length]
    exact valid
  · intro position valid different
    exact GeneralBorrowFreshReuseProtection.protection_position tree index parent parentNode _ vacant present location location
      protections fits position (by omega) different

end DuplicatePrefix.S02ConstructorOutsideProjection

open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S02ConstructorOutsideProjection.append_extension,
      ``DuplicatePrefix.S02ConstructorOutsideProjection.reuse_extension] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
