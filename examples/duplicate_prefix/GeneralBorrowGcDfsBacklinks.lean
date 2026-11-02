import duplicate_prefix.GeneralBorrowGcDfsIncoming

namespace DuplicatePrefix.GeneralBorrowGcDfsBacklinks
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem node_view (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node) :
    ∃ valid : index.toNat < (source_normal_projection tree location protections).topology.nodes.size,
      (source_normal_projection tree location protections).topology.nodes[index.toNat] =
        ⟨node.parent.map UniIndex.toNat,node.children.toList.map UniIndex.toNat⟩ := by
  have valid : index.toNat < (source_normal_projection tree location protections).topology.nodes.size := by
    have bounded := GeneralBorrowNodeUpdate.lookup_valid tree.nodes index node present
    unfold_general_projection;unfold_general_topology
    simpa only [Array.size_map] using bounded
  refine ⟨valid,?_⟩
  have shape := projection_topology_node tree location protections index.toNat index node rfl present
  simpa only [Array.getElem?_eq_getElem valid,Option.getD_some] using shape

/-- Exact original source backlinks are formed from actual parent lookup data
and the existing projected reciprocal Forest. -/
theorem of_forest (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (depth : ParentDepth tree.nodes) : GeneralBorrowGcDfsIncoming.Backlinks tree := by
  intro child node present parent edge
  obtain ⟨parentNode,parentPresent,_⟩ := depth.parent child node present parent edge
  obtain ⟨valid,shape⟩ := node_view tree location protections child node present
  obtain ⟨parentValid,parentShape⟩ := node_view tree location protections parent parentNode parentPresent
  have projectedEdge : (source_normal_projection tree location protections).topology.nodes[child.toNat].parent = some parent.toNat := by
    rw [shape,edge];rfl
  have member := (forest.parentChild child.toNat valid parent.toNat projectedEdge).2
  rw [parentShape] at member
  obtain ⟨originalChild,originalMember,same⟩ := List.mem_map.mp member
  have equal := GeneralBorrowNodeUpdate.index_injective originalChild child same
  exact ⟨parentNode,parentPresent,equal ▸ originalMember⟩

end DuplicatePrefix.GeneralBorrowGcDfsBacklinks
