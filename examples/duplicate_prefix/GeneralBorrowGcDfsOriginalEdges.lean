import duplicate_prefix.GeneralBorrowGcDfsFormation

namespace DuplicatePrefix.GeneralBorrowGcDfsOriginalEdges
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

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

/-- Projected reciprocal Forest plus real child closure reconstructs exact
ORIGINAL UniIndex parent edges. The source DFS parent certificates are thus
formed from the existing graph contract, rather than supplied separately. -/
theorem children (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (closed : GeneralBorrowGraph.ChildNodes tree) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) :
    ∀ child ∈ node.children.toList, ∃ childNode, tree.nodes.get child = some childNode ∧ childNode.parent = some index := by
  intro child member
  obtain ⟨childNode,childPresent⟩ := closed index node present child member
  obtain ⟨valid,shape⟩ := node_view tree location protections index node present
  obtain ⟨childValid,childShape⟩ := node_view tree location protections child childNode childPresent
  have projectedMember : child.toNat ∈ (source_normal_projection tree location protections).topology.nodes[index.toNat].children := by
    rw [shape]
    exact List.mem_map.mpr ⟨child,member,rfl⟩
  have projectedEdge := (forest.childParent index.toNat valid child.toNat projectedMember).2
  rw [childShape] at projectedEdge
  refine ⟨childNode,childPresent,?_⟩
  cases edge : childNode.parent with
  | none => simp only [edge,Option.map_none] at projectedEdge;cases projectedEdge
  | some parent =>
    simp only [edge,Option.map_some,Option.some.injEq] at projectedEdge
    have equal := GeneralBorrowNodeUpdate.index_injective parent index projectedEdge
    exact congrArg some equal

end DuplicatePrefix.GeneralBorrowGcDfsOriginalEdges
