import duplicate_prefix.GeneralBorrowExposedKnownRootPrimaryWitness
import duplicate_prefix.GeneralBorrowProjection
namespace DuplicatePrefix.GeneralBorrowExposedScopedReciprocal
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Projected forest reciprocity recovers the exact physical child edge. -/
theorem of_forest (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) :
    GeneralBorrowExposedNonleafPrimaryPath.Reciprocal tree := by
  intro child node present parent edge
  obtain ⟨parentNode,parentPresent,smaller⟩ := depth.parent child node present parent edge
  let topology := (source_normal_projection tree location protections).topology
  have size : topology.nodes.size = tree.nodes.data.size := by
    unfold topology
    unfold_general_projection
    unfold_general_topology
    simp only [Array.size_map]
  have childValid : child.toNat < topology.nodes.size := by
    rw [size]
    exact GeneralBorrowNodeUpdate.lookup_valid tree.nodes child node present
  have parentValid : parent.toNat < topology.nodes.size := by
    rw [size]
    exact GeneralBorrowNodeUpdate.lookup_valid tree.nodes parent parentNode parentPresent
  have childProjection := projection_topology_node tree location protections child.toNat child node rfl present
  have parentProjection := projection_topology_node tree location protections parent.toNat parent parentNode rfl parentPresent
  change (topology.nodes[child.toNat]?.getD ⟨none,[]⟩) = _ at childProjection
  change (topology.nodes[parent.toNat]?.getD ⟨none,[]⟩) = _ at parentProjection
  simp only [Array.getElem?_eq_getElem childValid,Option.getD_some] at childProjection
  simp only [Array.getElem?_eq_getElem parentValid,Option.getD_some] at parentProjection
  have projectedEdge : (topology.nodes[child.toNat]'childValid).parent = some parent.toNat := by
    rw [childProjection]
    simp only [edge,Option.map_some]
  have member := (forest.parentChild child.toNat childValid parent.toNat projectedEdge).2
  rw [parentProjection] at member
  obtain ⟨actual,actualMember,equal⟩ := List.mem_map.mp member
  have same : actual = child := GeneralBorrowNodeUpdate.index_injective actual child equal
  subst actual
  exact ⟨parentNode,parentPresent,actualMember⟩
end DuplicatePrefix.GeneralBorrowExposedScopedReciprocal
