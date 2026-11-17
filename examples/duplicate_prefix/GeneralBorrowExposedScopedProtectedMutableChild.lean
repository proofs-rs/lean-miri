import duplicate_prefix.GeneralBorrowFreshMixedChild
import duplicate_prefix.GeneralBorrowFreshChild
import duplicate_prefix.GeneralBorrowExposedScopedOwnership
namespace DuplicatePrefix.GeneralBorrowExposedScopedProtectedMutableChild
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowFreshMaterialization
open GeneralBorrowFreshMixedChild (extend)
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- Mutable-child formation extends ownership only in its selected component. -/
theorem mixed_extension (support : Nat → Prop) (before after : NormalTreeState) (parent child : Nat)
    (old : GeneralBorrowExposedScopedOwnership.Pointwise support before (fun _=>true) (GeneralBorrowAnchor.relation before parent))
    (oldPosition : ∀ position, position < after.locationStates.size → position ≠ child → position < before.locationStates.size)
    (states : ∀ position, position < before.locationStates.size → position ≠ child → after.stateAt position = before.stateAt position)
    (protections : ∀ position, position < before.locationStates.size → position ≠ child → after.protectedNodes.contains position = before.protectedNodes.contains position)
    (path : after.topology.ancestorPath child = child :: before.topology.ancestorPath parent)
    (newState : after.stateAt child = some GeneralBorrowFreshChild.inside) :
    GeneralBorrowExposedScopedOwnership.Pointwise (fun position => support position ∨ position = child) after (fun _=>true) (GeneralBorrowAnchor.relation after child) := by
  intro position supported valid
  by_cases fresh : position = child
  · subst position
    refine ⟨GeneralBorrowFreshChild.inside,newState,?_⟩
    simp only []
    change GeneralBorrowPermissions.Required _ true (GeneralBorrowAnchor.relation after child child) _
    have localRelation : GeneralBorrowAnchor.relation after child child = .LocalAccess := by
      unfold GeneralBorrowAnchor.relation
      rw [path]
      simp
    rw [localRelation]
    exact GeneralBorrowPermissions.fresh_mutable_owned .None true (after.protectedNodes.contains child)
  · have oldValid := oldPosition position valid fresh
    obtain ⟨state,present,permitted⟩ := old position (supported.resolve_right fresh) oldValid
    refine ⟨state,(states position oldValid fresh).trans present,?_⟩
    have related : GeneralBorrowAnchor.relation after child position = GeneralBorrowAnchor.relation before parent position := by
      unfold GeneralBorrowAnchor.relation
      rw [path]
      simp only [List.mem_cons,fresh,false_or]
    simpa only [related,protections position oldValid fresh] using permitted

theorem append_location (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode)
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
  have extension := GeneralBorrowFreshProjection.topology_extension tree index parent parentNode (GeneralBorrowFreshChild.child tag parent)
    atEnd parentPresent rfl rfl location nextLocation protections
  have beforeSizes := GeneralBorrowProjection.projection_sizes tree location protections
  have nextSizes := GeneralBorrowProjection.projection_sizes next nextLocation protections
  have topologySize : (source_normal_projection tree location protections).topology.nodes.size = tree.nodes.data.size := by
    unfold_general_projection
    unfold_general_topology
    simp only [Array.size_map]
  have afterSize : (source_normal_projection next nextLocation protections).locationStates.size = tree.nodes.data.size+1 := by
    have projectedSize : (source_normal_projection next nextLocation protections).locationStates.size =
        (source_normal_projection next nextLocation protections).topology.nodes.size := by
      unfold_general_projection
      unfold_general_topology
      simp only [Array.size_mapIdx,Array.size_map]
    rw [projectedSize,extension.length,topologySize]
  apply mixed_extension support (source_normal_projection tree location protections)
    (source_normal_projection next nextLocation protections) parent.toNat index.toNat owned
  · intro position valid different
    rw [afterSize] at valid
    rw [beforeSizes.1]
    omega
  · intro position valid different
    have bounded : position < tree.nodes.data.size := by rw [beforeSizes.1] at valid;exact valid
    exact GeneralBorrowFreshMaterialization.state_old tree index parent parentNode (GeneralBorrowFreshChild.child tag parent)
      atEnd parentPresent location GeneralBorrowFreshChild.inside protections position bounded
  · intro position valid different
    have bounded : position < tree.nodes.data.size := by rw [beforeSizes.1] at valid;exact valid
    exact GeneralBorrowFreshMaterialization.protection_old tree index parent parentNode (GeneralBorrowFreshChild.child tag parent)
      atEnd parentPresent location nextLocation protections position bounded
  · exact GeneralBorrowFreshProjection.projected_ancestors tree index parent parentNode (GeneralBorrowFreshChild.child tag parent)
      atEnd parentPresent rfl rfl location nextLocation protections forest
  · exact GeneralBorrowFreshMaterialization.state_new tree index parent parentNode (GeneralBorrowFreshChild.child tag parent)
      atEnd parentPresent location GeneralBorrowFreshChild.inside protections


end DuplicatePrefix.GeneralBorrowExposedScopedProtectedMutableChild
