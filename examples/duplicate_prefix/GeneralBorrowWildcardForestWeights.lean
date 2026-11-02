import duplicate_prefix.GeneralBorrowForestWeights
import duplicate_prefix.GeneralBorrowWildcardSubtreeData

namespace DuplicatePrefix.GeneralBorrowWildcardForestWeights
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.BorrowRangeAccess
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- Canonical raw BorrowTree work potential obtained from finite descendant
cardinality in the real source topology. No access-result premise is used. -/
def of_forest (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology) :
    GeneralBorrowWildcardSubtreeData.Weights tree := by
  let topology := (source_normal_projection tree location protections).topology
  refine ⟨fun index => GeneralBorrowForestWeights.weight topology index.toNat,?_⟩
  intro index node present
  have valid : index.toNat < topology.nodes.size := by
    have bounded := GeneralBorrowNodeUpdate.lookup_valid tree.nodes index node present
    dsimp only [topology]
    unfold_general_projection;unfold_general_topology
    simpa only [Array.size_map] using bounded
  have shape : topology.nodes[index.toNat] = ⟨node.parent.map UniIndex.toNat,node.children.toList.map UniIndex.toNat⟩ := by
    have shape := projection_topology_node tree location protections index.toNat index node rfl present
    dsimp only [topology] at valid ⊢
    simpa only [Array.getElem?_eq_getElem valid,Option.getD_some] using shape
  have bound := GeneralBorrowForestWeights.children topology forest index.toNat valid
  rw [shape] at bound
  simpa only [List.map_map,Function.comp_def] using bound

/-- Every component's potential is bounded by the tree's physical slot count,
including sparse vacant slots. -/
theorem bounded (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (root : UniIndex) : (of_forest tree location protections forest).weight root ≤ tree.nodes.size := by
  have bound := GeneralBorrowForestWeights.bounded (source_normal_projection tree location protections).topology root.toNat
  have size : (source_normal_projection tree location protections).topology.nodes.size = tree.nodes.size := by
    unfold_general_projection;unfold_general_topology
    simp only [Array.size_map,UniValMap.size]
  rw [size] at bound
  exact bound

end
end DuplicatePrefix.GeneralBorrowWildcardForestWeights
