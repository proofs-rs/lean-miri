import duplicate_prefix.GeneralBorrowCompatibleNormalPossible
import duplicate_prefix.GeneralBorrowCompatibleLocationSifaConsistency

namespace DuplicatePrefix.GeneralBorrowCompatibleNormalRuntime
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection
set_option autoImplicit false

/-- Installing one actual normal-access row preserves the complete call-time
RuntimeFacts: graph/allocator/SIFA/vacant Clean, exposure-cache coherence,
physical state possibility and tag high-water. The reference permission is
initial scalar data; no successful operation or history is assumed. This is
one normal phase, not the later other-root callbacks or whole invocation. -/
theorem after_row (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (position : Nat) (valid : position < tree.locations.entries.size)
    (anchor : UniIndex)
    (authorization : DuplicatePrefixBorrowAuthorization.Normal tree
      tree.locations.entries[position].data global.protectedTags anchor)
    (anchorNode : TreeNode) (present : tree.nodeAt anchor = some anchorNode)
    (kind : AccessKind) (mode : ChildrenVisitMode) :
    let location := tree.locations.entries[position].data
    let result := tree.performNormalAccessAt location anchor kind global.protectedTags mode
    let after := {tree with locations := GeneralRangeMapState.replaced tree.locations position valid result.location}
    result.access.status = .Completed ∧ result.outcome = .ok () ∧
    DuplicatePrefixBorrowContract.RuntimeFacts after global := by
  let location := tree.locations.entries[position].data
  let result := tree.performNormalAccessAt location anchor kind global.protectedTags mode
  let locations := GeneralRangeMapState.replaced tree.locations position valid result.location
  let after := {tree with locations := locations}
  have owned : GeneralBorrowCompatibleScopedNormal.Owned
      (source_normal_projection tree location global.protectedTags) anchor.toNat kind authorization.component := by
    intro index included bounded
    have size : (source_normal_projection tree location global.protectedTags).topology.nodes.size = tree.nodes.data.size := by
      unfold_general_projection
      unfold_general_topology
      simp only [Array.size_map]
    exact authorization.permissions kind index included (by rw [←size]; exact bounded)
  have formed := GeneralBorrowCompatibleLocationSifaConsistency.formed_after_row tree global.protectedTags
    runtime.formed position valid anchor anchorNode present kind mode authorization.component owned
  have coherence := GeneralBorrowCompatibleScopedNormalExposure.of_call_authorization_at
    tree global runtime position valid anchor authorization anchorNode present kind mode
  obtain ⟨forest⟩ := runtime.formed.forest location global.protectedTags
  have geometry := GeneralBorrowExposedScopedNormalMetadata.valid_aligned tree location global.protectedTags anchor anchorNode present
  have possible := GeneralBorrowCompatibleNormalPossible.normal tree location global.protectedTags anchor kind mode
    runtime.formed.fits forest geometry.1 authorization (runtime.possible position valid)
  refine ⟨formed.1, formed.2.1, {formed := formed.2.2.1, coherent := ?_, possible := ?_, below := ?_}⟩
  · exact GeneralRangeMapState.replaced_every (fun row =>
      GeneralBorrowExposureCardinality.LocationCoherent after row global.protectedTags)
      tree.locations position valid result.location runtime.coherent coherence.2.2
  · exact GeneralRangeMapState.replaced_every (fun (row : LocationTree) => ∀ index node, after.nodeAt index = some node →
      ((row.perms.get index).getD node.defaultLocationState).possible = true)
      tree.locations position valid result.location runtime.possible possible
  · exact ⟨runtime.below.mapping, runtime.below.protectors⟩

end DuplicatePrefix.GeneralBorrowCompatibleNormalRuntime
