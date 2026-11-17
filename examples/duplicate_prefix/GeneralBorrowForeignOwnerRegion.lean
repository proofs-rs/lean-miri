import duplicate_prefix.GeneralBorrowForestRegionOwnerMerge
import duplicate_prefix.GeneralBorrowRangePreserves

namespace DuplicatePrefix.GeneralBorrowForeignOwnerRegion
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Anchor ownership gives the STRONG ForeignOwned contract at every present
node outside its ancestor path, for either ownership kind. -/
theorem foreign (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor index : UniIndex) (node : TreeNode) (kind : AccessKind)
    (present : tree.nodeAt index = some node)
    (owner : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location protections) anchor.toNat kind)
    (outside : index.toNat ∉ (source_normal_projection tree location protections).topology.ancestorPath anchor.toNat) :
    GeneralBorrowPermissions.ForeignOwned (GeneralBorrowWildcardVirtualLeaf.effective location index node)
      (protections.contains node.tag) := by
  obtain ⟨bounded,_⟩ := array_of_node tree index node present
  have valid : index.toNat < (source_normal_projection tree location protections).topology.nodes.size := by
    unfold_general_projection
    unfold_general_topology
    simpa only [Array.size_map] using bounded
  obtain ⟨state,stored,owned⟩ := owner.permissions index.toNat valid
  rw [projection_state tree location protections index.toNat index node (GeneralBorrowProjection.index_self index) rfl present] at stored
  have equal : GeneralBorrowWildcardVirtualLeaf.effective location index node = state := Option.some.inj stored
  rw [←equal,GeneralBorrowAnchor.relation,ite_eq_right outside] at owned
  rw [GeneralBorrowForestRegionOwnerMerge.held_present tree location protections index node present] at owned
  cases kind <;> exact owned

end DuplicatePrefix.GeneralBorrowForeignOwnerRegion
