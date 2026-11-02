import duplicate_prefix.GeneralBorrowExposedScopedProtectedMutableChild
import duplicate_prefix.GeneralBorrowFreshReuseState
import duplicate_prefix.GeneralBorrowFreshReuseProtection
import duplicate_prefix.GeneralBorrowFreshReuseProjection
namespace DuplicatePrefix.GeneralBorrowExposedScopedProtectedMutableReuseChild
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowFreshMaterialization
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
theorem reuse_location (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (bounded : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (fits : tree.nodes.data.size ≤ 4294967296) (parentPresent : tree.nodeAt parent = some parentNode)
    (location : LocationTree) (protections : ProtectedTags)
    (support : Nat → Prop)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (owned : GeneralBorrowExposedScopedOwnership.Pointwise support (source_normal_projection tree location protections)
      (fun _=>true) (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) parent.toNat)) :
    GeneralBorrowExposedScopedOwnership.Pointwise (fun position => support position ∨ position = index.toNat)
      (source_normal_projection (GeneralBorrowFreshGraph.attached tree index parent parentNode (GeneralBorrowFreshChild.child tag parent))
        (materialized location index GeneralBorrowFreshChild.inside) protections)
      (fun _=>true)
      (GeneralBorrowAnchor.relation (source_normal_projection
        (GeneralBorrowFreshGraph.attached tree index parent parentNode (GeneralBorrowFreshChild.child tag parent))
        (materialized location index GeneralBorrowFreshChild.inside) protections) index.toNat) := by
  let next := GeneralBorrowFreshGraph.attached tree index parent parentNode (GeneralBorrowFreshChild.child tag parent)
  let nextLocation := materialized location index GeneralBorrowFreshChild.inside
  have beforeSizes := GeneralBorrowProjection.projection_sizes tree location protections
  have nextSizes := GeneralBorrowProjection.projection_sizes next nextLocation protections
  have topologySize : (source_normal_projection tree location protections).topology.nodes.size = tree.nodes.data.size := by
    unfold_general_projection
    unfold_general_topology
    simp only [Array.size_map]
  have afterSize : (source_normal_projection next nextLocation protections).locationStates.size = tree.nodes.data.size := by
    rw [nextSizes.1]
    exact GeneralBorrowFreshReuseState.attached_size tree index parent parentNode (GeneralBorrowFreshChild.child tag parent) bounded vacant parentPresent
  apply GeneralBorrowExposedScopedProtectedMutableChild.mixed_extension support (source_normal_projection tree location protections)
    (source_normal_projection next nextLocation protections) parent.toNat index.toNat owned
  · intro position valid different
    rw [afterSize] at valid
    rw [beforeSizes.1]
    omega
  · intro position valid different
    have bounded : position < tree.nodes.data.size := by rw [beforeSizes.1] at valid;exact valid
    exact GeneralBorrowFreshReuseState.state_old tree index parent parentNode (GeneralBorrowFreshChild.child tag parent)
      ‹index.toNat < tree.nodes.data.size› vacant parentPresent fits location GeneralBorrowFreshChild.inside protections position bounded different
  · intro position valid different
    have bounded : position < tree.nodes.data.size := by rw [beforeSizes.1] at valid;exact valid
    exact GeneralBorrowFreshReuseProtection.protection_position tree index parent parentNode (GeneralBorrowFreshChild.child tag parent)
      vacant parentPresent location nextLocation protections fits position bounded different
  · exact GeneralBorrowFreshReuseProjection.projected_ancestors tree index parent parentNode (GeneralBorrowFreshChild.child tag parent)
      bounded vacant parentPresent rfl rfl location nextLocation protections forest
  · exact GeneralBorrowFreshReuseState.state_new tree index parent parentNode (GeneralBorrowFreshChild.child tag parent)
      bounded vacant parentPresent location GeneralBorrowFreshChild.inside protections

end DuplicatePrefix.GeneralBorrowExposedScopedProtectedMutableReuseChild
