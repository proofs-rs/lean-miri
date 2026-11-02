import duplicate_prefix.DuplicatePrefixBorrowAuthorization
import duplicate_prefix.GeneralBorrowCompatibleScopedNormalExposure
namespace DuplicatePrefix.DuplicatePrefixNormalKind
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Internal operation-specific normal capability. A shared helper source
needs Read only; this does not weaken or replace the public S01 Both Normal. -/
structure Capability (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (source : UniIndex) (kind : AccessKind) where
  component : GeneralBorrowExposedScopedNormal.Component
    (source_normal_projection tree default protections).topology source.toNat
  permissions : ∀ index, component.support index → index < tree.nodes.data.size →
    ∃ state, (source_normal_projection tree location protections).stateAt index = some state ∧
      DuplicatePrefixScalarAuthorization.Compatible state kind
        (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) source.toNat index)
        ((source_normal_projection tree location protections).protectedNodes.contains index)

def of_normal (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (source : UniIndex) (normal : DuplicatePrefixBorrowAuthorization.Normal tree location protections source)
    (kind : AccessKind) : Capability tree location protections source kind :=
  ⟨normal.component,normal.permissions kind⟩

/-- The per-kind capability directly derives the actual normal operation,
with cache preservation from raw graph/coherence resources. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (source : UniIndex) (kind : AccessKind) (mode : ChildrenVisitMode)
    (capability : Capability tree location protections source kind)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (node : TreeNode) (present : tree.nodeAt source = some node)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections) :
    (tree.performNormalAccessAt location source kind protections mode).access.status = .Completed ∧
    (tree.performNormalAccessAt location source kind protections mode).outcome = .ok () ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree
      (tree.performNormalAccessAt location source kind protections mode).location protections := by
  obtain ⟨forest⟩ := formed.forest location protections
  obtain ⟨depth⟩ := formed.depth
  apply GeneralBorrowCompatibleScopedNormalExposure.access tree location protections source kind mode depth formed.children node present
    forest capability.component _ coherent
  intro index supported bounded
  have size : (source_normal_projection tree location protections).topology.nodes.size = tree.nodes.data.size := by
    unfold_general_projection
    unfold_general_topology
    simp only [Array.size_map]
  exact capability.permissions index supported (by rw [←size];exact bounded)

end DuplicatePrefix.DuplicatePrefixNormalKind
