import duplicate_prefix.GeneralBorrowGcDfsReadyPlan
import duplicate_prefix.GeneralBorrowGcDfsParentPaths

namespace DuplicatePrefix.GeneralBorrowGcDfsReadyFormation
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowForest
open DuplicatePrefix.GeneralBorrowGcDfsStage DuplicatePrefix.GeneralBorrowGcStrictChildren
open DuplicatePrefix.GeneralBorrowGcDfsPending
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- The unchanged original reciprocal Forest supplies all DFS source metadata
certificates, including source UniIndex child distinctness. -/
theorem metadata (original : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (forest : Forest (source_normal_projection original location protections).topology)
    (closed : GeneralBorrowGraph.ChildNodes original) : GeneralBorrowGcDfsReadyPlan.Metadata original where
  distinct := by
    intro index node present
    have valid : index.toNat < (source_normal_projection original location protections).topology.nodes.size := by
      have bounded := GeneralBorrowNodeUpdate.lookup_valid original.nodes index node present
      unfold_general_projection;unfold_general_topology
      simpa only [Array.size_map] using bounded
    have shape : (source_normal_projection original location protections).topology.nodes[index.toNat] =
        ⟨node.parent.map UniIndex.toNat,node.children.toList.map UniIndex.toNat⟩ := by
      have shape := projection_topology_node original location protections index.toNat index node rfl present
      simpa only [Array.getElem?_eq_getElem valid,Option.getD_some] using shape
    have distinct := forest.childrenDistinct index.toNat valid
    rw [shape] at distinct
    exact (List.pairwise_map.mp distinct).imp (fun different same => different (congrArg UniIndex.toNat same))
  children := GeneralBorrowGcDfsOriginalEdges.children original location protections forest closed

/-- Canonical initialization joins arbitrary branching/depth Plan formation to
arbitrarily many actual postvisits, retaining original pending nodes and fully
repaired outgoing child arrays of all completed surviving nodes. Final processed
indices are the exact original-metadata finite postorder, not an unknown set. -/
theorem children (original : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (forest : Forest (source_normal_projection original location protections).topology)
    (closed : GeneralBorrowGraph.ChildNodes original) (root : UniIndex) (node : TreeNode)
    (present : original.nodes.get root = some node) (live : Array BorTag) :
    ∃ after, source_gc_children original root live = ⟨after,.ok ()⟩ ∧
      Stage original (GeneralBorrowGcDfsFormation.unroll original original.nodes.size root).order.reverse after ∧
      Pending original (GeneralBorrowGcDfsFormation.unroll original original.nodes.size root).order.reverse after ∧
      GeneralBorrowGcDfsReciprocalStage.Reciprocal (GeneralBorrowGcDfsFormation.unroll original original.nodes.size root).order.reverse after ∧
      Ranked (fun index => forest.rank index.toNat) after ∧ after.nodes.size = original.nodes.size := by
  let weights := GeneralBorrowWildcardForestWeights.of_forest original location protections forest
  let shape := GeneralBorrowGcDfsFormation.unroll original original.nodes.size root
  have enough := GeneralBorrowWildcardForestWeights.bounded original location protections forest root
  have valid := GeneralBorrowGcDfsFormation.unroll_valid original weights closed original.nodes.size root node present enough
  have distinct := (GeneralBorrowGcDfsFormation.order_properties original location protections forest shape valid).2
  have lengthBound := GeneralBorrowGcDfsFormation.order_bounded original weights shape valid
  have rootEq : shape.root = root := GeneralBorrowGcDfsFormation.unroll_root original original.nodes.size root
  rw [rootEq] at lengthBound
  change shape.order.length ≤ (GeneralBorrowWildcardForestWeights.of_forest original location protections forest).weight root at lengthBound
  have plan := GeneralBorrowGcDfsShape.plan original shape valid distinct
  rw [rootEq] at plan
  let originalMetadata := metadata original location protections forest closed
  have ranked : Ranked (fun index => forest.rank index.toNat) original := by
    intro index current lookup child member
    obtain ⟨childNode,childPresent,childEdge⟩ := originalMetadata.children index current lookup child member
    exact (GeneralBorrowGcDfsParentPaths.original_edge original location protections forest child childNode childPresent index childEdge).2
  have stage : Stage original [] original := ⟨by intro index outside;rfl,by intro index member;simp at member⟩
  obtain ⟨after,actual,finalStage,finalRank,finalPending,finalRepaired,capacity⟩ := GeneralBorrowGcDfsReadyPlan.execute
    (fun index => forest.rank index.toNat) original original root live originalMetadata plan original 0 stage ranked
    (GeneralBorrowGcDfsPending.initial original) (GeneralBorrowGcDfsReciprocalStage.initial original) (by omega)
  refine ⟨after,?_,finalStage,finalPending,finalRepaired,finalRank,capacity⟩
  rw [GeneralBorrowGcWalker.children_equation,actual]

/-- Every original parentless root survives any real component child-GC walk
with its original tag and parent=None, even when the visited component is a
different tree or a proper descendant. -/
theorem roots_retained (original : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (forest : Forest (source_normal_projection original location protections).topology)
    (closed : GeneralBorrowGraph.ChildNodes original) (root : UniIndex) (node : TreeNode)
    (present : original.nodes.get root = some node) (live : Array BorTag)
    (other : UniIndex) (originalNode : TreeNode) (originalPresent : original.nodes.get other = some originalNode)
    (parentless : originalNode.parent = none) :
    ∃ current, (source_gc_children original root live).tree.nodes.get other = some current ∧
      current.parent = none ∧ current.tag = originalNode.tag := by
  obtain ⟨after,actual,_,pending,_,_,_⟩ := children original location protections forest closed root node present live
  obtain ⟨current,lookup,edge,tag⟩ := pending other originalNode originalPresent (.inl parentless)
  refine ⟨current,?_,edge.trans parentless,tag⟩
  rw [actual]
  exact lookup

end
end DuplicatePrefix.GeneralBorrowGcDfsReadyFormation
