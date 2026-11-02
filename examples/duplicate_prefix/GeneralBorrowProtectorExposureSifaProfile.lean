import duplicate_prefix.GeneralBorrowSifaProtectionProfile
import duplicate_prefix.GeneralBorrowProtectorReleaseExposureCache
namespace DuplicatePrefix.GeneralBorrowProtectorExposureSifaProfile
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowLocationSifaConsistency DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowExposureRelease DuplicatePrefix.GeneralBorrowExposureMapFrame
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- The actual exposure-cache release phase preserves all physical SIFA bounds
and Clean under both still-current and removed protector tables. Cache
cardinality is a separate invariant; no cache coherence is assumed here. -/
theorem release (tree : BorrowTree) (protections : ProtectedTags) (index : UniIndex) (node : TreeNode)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (present : tree.nodeAt index = some node) (tagged : tree.indexOfTag node.tag = some index)
    (initial : Every (fun location => Profile tree location protections) tree.locations) :
    (tree.updateExposureForProtectorRelease node.tag).outcome = .ok () ∧
    Every (fun location => Profile (tree.updateExposureForProtectorRelease node.tag).tree location protections)
      (tree.updateExposureForProtectorRelease node.tag).tree.locations ∧
    Every (fun location => Profile (tree.updateExposureForProtectorRelease node.tag).tree location (protections.remove node.tag))
      (tree.updateExposureForProtectorRelease node.tag).tree.locations := by
  have phase : (tree.updateExposureForProtectorRelease node.tag).outcome = .ok () ∧
      Every (fun location => Profile (tree.updateExposureForProtectorRelease node.tag).tree location protections)
        (tree.updateExposureForProtectorRelease node.tag).tree.locations := by
    cases exposed : node.isExposed with
    | false =>
      have actual : tree.updateExposureForProtectorRelease node.tag = ⟨tree,.ok ()⟩ := by
        simp [BorrowTree.updateExposureForProtectorRelease,tagged,present,exposed]
      rw [actual]
      exact ⟨rfl,initial⟩
    | true =>
      let update := GeneralBorrowProtectorReleaseExposureCache.callback tree index node
      have each : ∀ location,Profile tree location protections →
          (update location).2 = .ok () ∧ Profile tree (update location).1 protections := by
        intro location good
        have cacheSuccess := GeneralBorrowExposure.update_exposure_succeeds location.exposedCache tree.nodes depth index node present
          (((location.perms.get index).getD node.defaultLocationState).permission.strongestAllowedLocalAccess true)
          (((location.perms.get index).getD node.defaultLocationState).permission.strongestAllowedLocalAccess false)
        refine ⟨?_,GeneralBorrowSifaProtectionProfile.perms tree location (update location).1 protections rfl good⟩
        change (location.exposedCache.updateExposure tree.nodes index _ _).outcome.mapError _ = .ok ()
        rw [cacheSuccess];rfl
      have all := GeneralBorrowLocationUpdateProperty.every tree update
        (fun location => Profile tree location protections) (fun location => Profile tree location protections) initial each
      have graph := GeneralBorrowLocationUpdateFrame.nodes tree update
      have actual : tree.updateExposureForProtectorRelease node.tag = source_location_update tree update := by
        unfold BorrowTree.updateExposureForProtectorRelease
        simp only [tagged,present,exposed,Bool.not_true,Bool.false_eq_true,↓reduceIte,Id.run,pure]
        rfl
      rw [actual]
      refine ⟨all.1,?_⟩
      intro position valid
      exact GeneralBorrowSifaProtectionProfile.nodes tree _ _ protections graph (all.2 position valid)
  refine ⟨phase.1,phase.2,?_⟩
  intro position valid
  exact GeneralBorrowSifaProtectionProfile.remove _ _ protections node.tag (phase.2 position valid)

end DuplicatePrefix.GeneralBorrowProtectorExposureSifaProfile
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectorExposureSifaProfile.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protector-exposure SIFA profile dependency {dependency}"
