import duplicate_prefix.GeneralBorrowDefaultNormalTables
import duplicate_prefix.GeneralBorrowFreshReuseAnchor
namespace DuplicatePrefix.GeneralBorrowDefaultMaterializedNormal
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowFreshDefaultChild GeneralBorrowFreshMaterialization
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem topology_size (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) :
    (source_normal_projection tree location protections).topology.nodes.size = tree.nodes.data.size := by
  unfold_general_projection
  unfold_general_topology
  simp only [Array.size_map]

/-- Real append attachment and inside mutable materialization form exact scalar
state/protector/path extension data, with arbitrary old permission states. -/
theorem append (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (atEnd : index.toNat = tree.nodes.data.size) (present : tree.nodeAt parent = some parentNode)
    (location : LocationTree) (protections : ProtectedTags) (unprotected : protections.contains tag = false)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology) :
    GeneralBorrowDefaultNormalTables.Extension (source_normal_projection tree location protections)
      (source_normal_projection (GeneralBorrowFreshGraph.attached tree index parent parentNode (child tag parent))
        (materialized location index inside) protections) parent.toNat index.toNat := by
  let afterLocation := materialized location index inside
  have extension := GeneralBorrowFreshProjection.topology_extension tree index parent parentNode (child tag parent)
    atEnd present rfl rfl location afterLocation protections
  have size := topology_size tree location protections
  have indexEq : index.toNat = (source_normal_projection tree location protections).topology.nodes.size := atEnd.trans size.symm
  have patch := GeneralBorrowFreshNormalComponent.of_append _ _ parent.toNat extension
  have paths := GeneralBorrowFreshSharedPaths.of_append _ _ parent.toNat extension forest
  rw [←indexEq] at patch paths
  refine ⟨patch,paths,?_,?_,?_,?_,?_⟩
  · intro query valid different
    rw [extension.length] at valid
    rw [indexEq] at different
    omega
  · intro query valid different
    exact GeneralBorrowFreshMaterialization.state_old tree index parent parentNode (child tag parent) atEnd present location inside protections query (by rw [←size];exact valid)
  · exact GeneralBorrowFreshMaterialization.state_new tree index parent parentNode (child tag parent) atEnd present location inside protections
  · intro query valid different
    exact GeneralBorrowFreshMaterialization.protection_old tree index parent parentNode (child tag parent) atEnd present location afterLocation protections query (by rw [←size];exact valid)
  · have newPresent := GeneralBorrowFreshGraph.new_lookup tree index parent parentNode (child tag parent) atEnd present
    rw [GeneralBorrowNormalPermissionMetadata.held _ afterLocation protections index (child tag parent) newPresent]
    exact unprotected

/-- The same exact table extension for a genuinely vacant reusable slot; old
optional permission slots need not be Clean inside the overwritten row. -/
theorem reuse (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (bounded : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (fits : tree.nodes.data.size ≤ 4294967296) (present : tree.nodeAt parent = some parentNode)
    (location : LocationTree) (protections : ProtectedTags) (unprotected : protections.contains tag = false)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology) :
    GeneralBorrowDefaultNormalTables.Extension (source_normal_projection tree location protections)
      (source_normal_projection (GeneralBorrowFreshGraph.attached tree index parent parentNode (child tag parent))
        (materialized location index inside) protections) parent.toNat index.toNat := by
  let afterLocation := materialized location index inside
  have extension := GeneralBorrowFreshReuseProjection.topology_extension tree index parent parentNode (child tag parent)
    bounded vacant present rfl rfl location afterLocation protections
  have size := topology_size tree location protections
  refine ⟨GeneralBorrowFreshNormalComponent.of_reuse _ _ index.toNat parent.toNat extension,
    GeneralBorrowFreshSharedPaths.of_reuse _ _ index.toNat parent.toNat extension forest,?_,?_,?_,?_,?_⟩
  · intro query valid different
    rw [extension.length] at valid
    exact valid
  · intro query valid different
    exact GeneralBorrowFreshReuseState.state_old tree index parent parentNode (child tag parent) bounded vacant present fits location inside protections query (by rw [←size];exact valid) different
  · exact GeneralBorrowFreshReuseState.state_new tree index parent parentNode (child tag parent) bounded vacant present location inside protections
  · intro query valid different
    exact GeneralBorrowFreshReuseProtection.protection_position tree index parent parentNode (child tag parent) vacant present location afterLocation protections fits query (by rw [←size];exact valid) different
  · rw [GeneralBorrowFreshReuseProtection.protection_new tree index parent parentNode (child tag parent) vacant present afterLocation protections]
    exact unprotected

end DuplicatePrefix.GeneralBorrowDefaultMaterializedNormal
