import duplicate_prefix.GeneralBorrowProtectorCacheMap
import duplicate_prefix.GeneralBorrowNormalExposureTodo
import duplicate_prefix.GeneralBorrowLocationUpdateFrame
namespace DuplicatePrefix.GeneralBorrowProtectorReleaseExposureCache
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposureCardinality DuplicatePrefix.GeneralBorrowExposureLevelUpdate
open DuplicatePrefix.GeneralBorrowExposureRelease DuplicatePrefix.GeneralBorrowExposureMapFrame
open DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] UniValMap.insert

def callback (tree : BorrowTree) (index : UniIndex) (node : TreeNode) (location : LocationTree) :
    LocationTree × Except BorrowTree.TreeMutationError Unit :=
  let state := (location.perms.get index).getD node.defaultLocationState
  let update := location.exposedCache.updateExposure tree.nodes index
    (state.permission.strongestAllowedLocalAccess true) (state.permission.strongestAllowedLocalAccess false)
  ({location with exposedCache := update.cache},update.outcome.mapError BorrowTree.TreeMutationError.ExposedCache)

private theorem other_tag (tree : BorrowTree) (index query : UniIndex) (node value : TreeNode)
    (tagged : tree.indexOfTag node.tag = some index)
    (nodeTags : ∀ index node,tree.nodeAt index = some node → tree.indexOfTag node.tag = some index)
    (present : tree.nodeAt query = some value) (different : query ≠ index) : value.tag ≠ node.tag := by
  intro same
  have lookup := nodeTags query value present
  rw [same,tagged] at lookup
  exact different (Option.some.inj lookup).symm

private theorem local_cache (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (protections : ProtectedTags) (index : UniIndex) (node : TreeNode)
    (present : tree.nodeAt index = some node) (tagged : tree.indexOfTag node.tag = some index)
    (nodeTags : ∀ index node,tree.nodeAt index = some node → tree.indexOfTag node.tag = some index)
    (held : protections.contains node.tag = true) (exposed : node.isExposed = true)
    (location : LocationTree) (initial : LocationCoherent tree location protections) :
    (callback tree index node location).2 = .ok () ∧
      LocationCoherent tree (callback tree index node location).1 (protections.remove node.tag) := by
  let state := (location.perms.get index).getD node.defaultLocationState
  let level := state.permission.strongestAllowedLocalAccess false
  have oldLevel : effective location protections index node = state.permission.strongestAllowedLocalAccess true := by
    simp only [effective,held,state]
  have success := GeneralBorrowExposure.update_exposure_succeeds location.exposedCache tree.nodes depth index node present
    (state.permission.strongestAllowedLocalAccess true) level
  have preserved := GeneralBorrowExposureLevelUpdate.preserves location.exposedCache tree.nodes depth
    (effective location protections) initial index node present exposed level
  rw [oldLevel] at preserved
  refine ⟨?_,?_⟩
  · change (location.exposedCache.updateExposure tree.nodes index (state.permission.strongestAllowedLocalAccess true) level).outcome.mapError _ = _
    rw [success];rfl
  · apply DuplicatePrefix.GeneralBorrowNormalExposureTodo.coherent_congr _ _ _ _ preserved
    intro query value found
    by_cases same : query = index
    · subst query
      have equal : value = node := Option.some.inj (found.symm.trans present)
      subst value
      simp only [replace,ite_true,effective,callback,ProtectedTags.contains,ProtectedTags.get_remove_same,
        Option.isSome_none,level,state]
    · have different := other_tag tree index query node value tagged nodeTags found same
      simp only [replace,ite_eq_right same,effective,callback,ProtectedTags.contains,
        GeneralBorrowProtectorCacheMap.remove_other protections node.tag value.tag different]

/-- The genuine exposure update before protector deletion preserves every
partition's cardinality invariant under the actual removed-tag table. This
handles arbitrary exposed flags and protections, retaining all source cache
updates. The earlier associatedAccess loop of releaseProtector is separate. -/
theorem release (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (protections : ProtectedTags) (index : UniIndex) (node : TreeNode)
    (present : tree.nodeAt index = some node) (tagged : tree.indexOfTag node.tag = some index)
    (nodeTags : ∀ index node,tree.nodeAt index = some node → tree.indexOfTag node.tag = some index)
    (held : protections.contains node.tag = true)
    (initial : Every (fun location => LocationCoherent tree location protections) tree.locations) :
    (tree.updateExposureForProtectorRelease node.tag).outcome = .ok () ∧
      Every (fun location => LocationCoherent (tree.updateExposureForProtectorRelease node.tag).tree location
        (protections.remove node.tag)) (tree.updateExposureForProtectorRelease node.tag).tree.locations := by
  cases exposed : node.isExposed with
  | false =>
    have actual : tree.updateExposureForProtectorRelease node.tag = ⟨tree,.ok ()⟩ := by
      simp [BorrowTree.updateExposureForProtectorRelease,tagged,present,exposed]
    rw [actual]
    refine ⟨rfl,?_⟩
    intro position valid
    apply GeneralBorrowProtectorCacheMap.frame tree _ protections _ (initial position valid)
    intro query value found flag
    have different : value.tag ≠ node.tag := by
      intro same
      have lookup := nodeTags query value found
      rw [same,tagged] at lookup
      have equal : query = index := (Option.some.inj lookup).symm
      subst query
      have valueEq : value = node := Option.some.inj (found.symm.trans present)
      subst value
      rw [exposed] at flag;cases flag
    unfold ProtectedTags.contains
    rw [GeneralBorrowProtectorCacheMap.remove_other protections node.tag value.tag different]
  | true =>
    let update := callback tree index node
    have all := GeneralBorrowLocationUpdateProperty.every tree update
      (fun location => LocationCoherent tree location protections)
      (fun location => LocationCoherent tree location (protections.remove node.tag)) initial
      (local_cache tree depth protections index node present tagged nodeTags held exposed)
    have nodes := GeneralBorrowLocationUpdateFrame.nodes tree update
    have actual : tree.updateExposureForProtectorRelease node.tag = source_location_update tree update := by
      unfold BorrowTree.updateExposureForProtectorRelease
      simp only [tagged,present,exposed,Bool.not_true,Bool.false_eq_true,↓reduceIte,Id.run,pure]
      rfl
    rw [actual]
    refine ⟨all.1,?_⟩
    intro position valid
    change Coherent _ (source_location_update tree update).tree.nodes _
    rw [nodes]
    exact all.2 position valid

end DuplicatePrefix.GeneralBorrowProtectorReleaseExposureCache
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectorReleaseExposureCache.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protector-release exposure dependency {dependency}"
