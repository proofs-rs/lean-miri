import duplicate_prefix.DuplicatePrefixNormalAuthorizationPreservation
import duplicate_prefix.GeneralBorrowExposedScopedNormalCache

namespace DuplicatePrefix.GeneralBorrowCompatibleNormalPossible
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection
set_option autoImplicit false

/-- Possibility for every present physical node is preserved by the real normal
phase. Inside the selected component it follows from preserved exact scalar
capabilities; outside, the actual stored permission is unchanged. -/
theorem normal (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (kind : AccessKind) (mode : ChildrenVisitMode)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (valid : anchor.toNat < (source_normal_projection tree location protections).topology.nodes.size)
    (authorization : DuplicatePrefixBorrowAuthorization.Normal tree location protections anchor)
    (possible : ∀ index node, tree.nodeAt index = some node →
      ((location.perms.get index).getD node.defaultLocationState).possible = true) :
    ∀ index node, tree.nodeAt index = some node →
      ((((tree.performNormalAccessAt location anchor kind protections mode).location).perms.get index).getD
        node.defaultLocationState).possible = true := by
  have aligned : (source_normal_projection tree location protections).locationStates.size =
      (source_normal_projection tree location protections).topology.nodes.size := by
    unfold_general_projection
    unfold_general_topology
    simp only [Array.size_mapIdx, Array.size_map]
  have preserved := GeneralBorrowCompatibleScopedPreservation.access_preserves tree location protections
    anchor kind mode fits forest valid aligned authorization.component
    (DuplicatePrefixNormalAuthorizationPreservation.pointwise tree location protections anchor authorization)
  intro index node present
  by_cases inside : authorization.component.support index.toNat
  · have bounded := GeneralBorrowNodeUpdate.lookup_valid tree.nodes index node present
    have afterValid : index.toNat < (source_normal_projection tree
        (tree.performNormalAccessAt location anchor kind protections mode).location protections).locationStates.size := by
      rw [(projection_sizes tree _ protections).1]
      exact bounded
    obtain ⟨state, stored, compatible⟩ := preserved index.toNat inside afterValid
    rw [projection_location_state tree _ protections index node present] at stored
    have stateEqual : ((tree.performNormalAccessAt location anchor kind protections mode).location.perms.get index).getD
        node.defaultLocationState = state := by
      simpa only [BorrowTree.locationStateAt, present, bind, pure, Option.bind_some, Option.some.injEq] using stored
    rw [stateEqual]
    exact compatible.1.1
  · rw [GeneralBorrowExposedScopedNormalCache.outside tree location protections anchor kind mode
      authorization.component index node present inside]
    exact possible index node present

end DuplicatePrefix.GeneralBorrowCompatibleNormalPossible
