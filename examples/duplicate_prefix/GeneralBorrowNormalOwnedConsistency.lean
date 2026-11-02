import duplicate_prefix.DuplicatePrefixNormalAuthorizationPreservation
import duplicate_prefix.GeneralBorrowLocationSifaConsistency

namespace DuplicatePrefix.GeneralBorrowNormalOwnedConsistency
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection
set_option autoImplicit false

/-- The extra local protected ReservedIM scalar case is excluded by the
independent real SIFA consistency invariant. Thus the old ownership library
can be reused without imposing stronger permissions on consistent rows. -/
theorem both_owned (state : LocationState) (related : AccessRelatedness) (held : Bool)
    (both : DuplicatePrefixScalarBothAuthorization.Both state related held)
    (consistent : GeneralBorrowSifaPermissionConsistency.Consistent state held) :
    GeneralBorrowPermissions.Owned state related held := by
  rcases (DuplicatePrefixScalarBothAuthorization.both_iff_owned_or_local_reserved state related held).mp both with owned | extra
  · exact owned
  · rcases extra with ⟨possible, localRelation, heldTrue, reserved⟩
    obtain ⟨strongest, actual, bound⟩ := consistent
    simp [Permission.strongestIdempotentForeignAccess, heldTrue, reserved] at actual

/-- Raw S01 Normal plus the physical SIFA profile supplies the legacy scoped
Write ownership contract, including arbitrary old-node permissions. -/
theorem normal_write (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (authorization : DuplicatePrefixBorrowAuthorization.Normal tree location protections anchor)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location protections) :
    GeneralBorrowExposedScopedNormal.Owned (source_normal_projection tree location protections)
      anchor.toNat .Write authorization.component := by
  have pointwise := DuplicatePrefixNormalAuthorizationPreservation.pointwise tree location protections anchor authorization
  have sifa := GeneralBorrowLocationSifaConsistency.projection tree location protections fits profile
  intro index supported valid
  have aligned : (source_normal_projection tree location protections).locationStates.size =
      (source_normal_projection tree location protections).topology.nodes.size := by
    unfold_general_projection
    unfold_general_topology
    simp only [Array.size_mapIdx, Array.size_map]
  obtain ⟨state, present, both⟩ := pointwise index supported (by rw [aligned]; exact valid)
  exact ⟨state, present, both_owned state _ _ both (sifa index state present)⟩

end DuplicatePrefix.GeneralBorrowNormalOwnedConsistency
