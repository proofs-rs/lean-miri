import duplicate_prefix.S02ConstructorOutsideProjection

namespace DuplicatePrefix.S02ConstructorOutsideGenericProjection
open Miri Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowFreshNode GeneralBorrowFreshGraph GeneralBorrowPresence
open S02ConstructorOutsideProjection (state_old)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
attribute [local irreducible] UniValMap.insert

/-- The untouched outside slot projects to the actual child's lazy default. -/
theorem state_new (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode)
    (location : LocationTree) (protections : ProtectedTags) (clean : location.perms.get index = none) :
    (source_normal_projection (attached tree index parent parentNode newNode) location protections).stateAt index.toNat =
      some newNode.defaultLocationState := by
  rw [projection_state _ _ _ index.toNat index _ (index_self index) rfl
    (GeneralBorrowFreshMetadataChildReuseGraph.new_lookup tree index parent parentNode newNode vacant parentPresent),clean]
  rfl

/-- Data-only projection consequences needed for an arbitrary destination's
full normal table. The fresh protector bit is unrestricted. -/
structure Extension (before after : NormalTreeState) (parent child : Nat) (state : LocationState) : Prop where
  paths : GeneralBorrowFreshSharedPaths.Attach before.topology after.topology parent child
  oldValid : ∀ position,position < after.topology.nodes.size → position ≠ child → position < before.topology.nodes.size
  oldState : ∀ position,position < before.topology.nodes.size → position ≠ child → after.stateAt position = before.stateAt position
  newState : after.stateAt child = some state
  oldProtected : ∀ position,position < before.topology.nodes.size → position ≠ child →
    after.protectedNodes.contains position = before.protectedNodes.contains position

 theorem topology_size (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) :
    (source_normal_projection tree location protections).topology.nodes.size = tree.nodes.data.size := by
  unfold_general_projection
  unfold_general_topology
  simp only [Array.size_map]

/-- Append creates the exact untouched destination-row projection extension. -/
theorem append_extension (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (atEnd : index.toNat = tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (present : tree.nodeAt parent = some parentNode) (fits : tree.nodes.data.size ≤ 4294967296)
    (childParent : newNode.parent = some parent) (leaf : newNode.children = #[])
    (location : LocationTree) (protections : ProtectedTags) (clean : location.perms.get index = none)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology) :
    Extension (source_normal_projection tree location protections)
      (source_normal_projection (attached tree index parent parentNode newNode)
        location protections) parent.toNat index.toNat newNode.defaultLocationState := by
  have ext := GeneralBorrowFreshProjection.topology_extension tree index parent parentNode newNode atEnd present childParent leaf location location protections
  have size := topology_size tree location protections
  have afterSize := topology_size (attached tree index parent parentNode newNode) location protections
  have indexEq : index.toNat = (source_normal_projection tree location protections).topology.nodes.size := atEnd.trans size.symm
  have paths := GeneralBorrowFreshSharedPaths.of_append _ _ parent.toNat ext forest
  rw [←indexEq] at paths
  refine ⟨paths,?_,?_,state_new tree index parent parentNode newNode vacant present location protections clean,?_⟩
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
theorem reuse_extension (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (bounded : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (present : tree.nodeAt parent = some parentNode) (fits : tree.nodes.data.size ≤ 4294967296)
    (childParent : newNode.parent = some parent) (leaf : newNode.children = #[])
    (location : LocationTree) (protections : ProtectedTags) (clean : location.perms.get index = none)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology) :
    Extension (source_normal_projection tree location protections)
      (source_normal_projection (attached tree index parent parentNode newNode)
        location protections) parent.toNat index.toNat newNode.defaultLocationState := by
  have ext := GeneralBorrowFreshReuseProjection.topology_extension tree index parent parentNode newNode bounded vacant present childParent leaf location location protections
  have size := topology_size tree location protections
  have afterSize := topology_size (attached tree index parent parentNode newNode) location protections
  refine ⟨GeneralBorrowFreshSharedPaths.of_reuse _ _ index.toNat parent.toNat ext forest,?_,?_,
    state_new tree index parent parentNode newNode vacant present location protections clean,?_⟩
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

end DuplicatePrefix.S02ConstructorOutsideGenericProjection

open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S02ConstructorOutsideGenericProjection.append_extension,
      ``DuplicatePrefix.S02ConstructorOutsideGenericProjection.reuse_extension] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
