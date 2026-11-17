import duplicate_prefix.GeneralBorrowExposedScopedReadFrameAccess
import duplicate_prefix.GeneralBorrowExposedScopedOwnership
namespace DuplicatePrefix.GeneralBorrowExposedScopedMixedAccess
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowExposedKnownRootState
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- The real selected-component normal Read and every other physical root call
preserve mixed mutable/read-only labels. Only initial raw resources are required. -/
theorem mixed (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (anchorNode selectedNode : TreeNode) (tail : List UniIndex)
    (mode : ChildrenVisitMode) (range : ByteRange)
    (roots : tree.roots = (head::tail).toArray)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (component : GeneralBorrowExposedScopedNormal.Component (source_normal_projection tree location protections).topology anchor.toNat)
    (owned : GeneralBorrowExposedScopedNormal.Owned (source_normal_projection tree location protections) anchor.toNat .Read component)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorPresent : tree.nodeAt anchor = some anchorNode) (selectedPresent : tree.nodes.get selected = some selectedNode)
    (rootPath : ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast! = selected.toNat)
    (hidden : ∀ index node,component.support index.toNat → tree.nodeAt index = some node → node.isExposed = false)
    (separate : ∀ index,area.support index → ¬component.support index.toNat)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (readable : Readable tree location protections)
    (tags : ∀ index node,area.support index → tree.nodes.get index = some node → node.tag.value ≤ selectedNode.tag.value)
    (primaryData : head ≠ selected → GeneralBorrowExposedKnownRootPrimaryWitness.Data tree location head protections)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (writable : Nat → Bool)
    (mixed : GeneralBorrowExposedScopedOwnership.Pointwise component.support
      (source_normal_projection tree location protections) writable
      (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat))
    (tailData : ∀ root ∈ tail,root ≠ selected → Data tree location root protections) :
    ∃ after,
      source_access_location (source_tree_access_at tree location (some anchor) .Read protections mode range) = after ∧
      source_access_status (source_tree_access_at tree location (some anchor) .Read protections mode range) = none ∧
      GeneralBorrowExposedScopedOwnership.Pointwise component.support
        (source_normal_projection tree after protections) writable
        (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat) := by
  obtain ⟨after,actual,status,fr,profile,coherent,frame⟩ :=
    GeneralBorrowExposedScopedReadFrameAccess.access tree location protections anchor selected head anchorNode selectedNode tail
      mode range roots forest component owned depth children anchorPresent selectedPresent rootPath hidden separate coherent readable tags primaryData tailData
  have sizes := GeneralBorrowProjection.projection_sizes tree location protections
  have topologySize : (source_normal_projection tree location protections).topology.nodes.size = tree.nodes.data.size := by
    unfold_general_projection
    unfold_general_topology
    simp only [Array.size_map]
  have valid : anchor.toNat < (source_normal_projection tree location protections).topology.nodes.size := by
    rw [topologySize]
    exact GeneralBorrowNodeUpdate.lookup_valid tree.nodes anchor anchorNode anchorPresent
  have normalMixed := GeneralBorrowExposedScopedOwnership.access_mixed tree location protections anchor .Read mode writable
    fits forest valid (sizes.1.trans topologySize.symm) component mixed (fun _ _ _ _ _ => rfl)
  refine ⟨after,actual,status,?_⟩
  exact GeneralBorrowExposedScopedOwnership.row_frame tree _ after protections component.support writable _ fits normalMixed
    (fun index member => frame index (fun included => separate index included member))

end DuplicatePrefix.GeneralBorrowExposedScopedMixedAccess
