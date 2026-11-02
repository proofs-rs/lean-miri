import duplicate_prefix.GeneralBorrowProtectedReadPermissionMetadata
import duplicate_prefix.GeneralBorrowProtectedReadRange
import duplicate_prefix.GeneralBorrowProtectedReadableStage
import duplicate_prefix.GeneralBorrowPositiveConstructorSifaProfile
import duplicate_prefix.GeneralBorrowProtectedReservationType
import duplicate_prefix.GeneralBorrowLocationUpdateFrame
import duplicate_prefix.GeneralBorrowPartitionExposeCardinality
import duplicate_prefix.GeneralBorrowSifaProtectionProfile
namespace DuplicatePrefix.GeneralBorrowTwoProtectedStateInfoConflict
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.BorrowRangeAccess
open DuplicatePrefix.GeneralBorrowExposureRelease DuplicatePrefix.GeneralBorrowExposureMapFrame
open DuplicatePrefix.GeneralBorrowConstructorPriorPermission
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

private theorem mark_profile (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (index : UniIndex) (node : TreeNode) (present : tree.nodeAt index = some node)
    (initial : GeneralBorrowLocationSifaConsistency.Profile tree location protections) :
    GeneralBorrowLocationSifaConsistency.Profile {tree with nodes := tree.nodes.insert index {node with isExposed := true}} location protections := by
  refine ⟨?_,?_⟩
  · intro query value found
    by_cases same : query = index
    · subst query
      change (tree.nodes.insert index {node with isExposed := true}).get index = some value at found
      rw [GeneralBorrowFreshLocation.get_same] at found
      cases found
      exact initial.present index node present
    · change (tree.nodes.insert index {node with isExposed := true}).get query = some value at found
      rw [GeneralBorrowFreshLocation.get_other _ index query _ same] at found
      exact initial.present query value found
  · intro query missing
    have different : query ≠ index := by
      intro same;subst query
      change (tree.nodes.insert index {node with isExposed := true}).get index = none at missing
      rw [GeneralBorrowFreshLocation.get_same] at missing;cases missing
    change (tree.nodes.insert index {node with isExposed := true}).get query = none at missing
    rw [GeneralBorrowFreshLocation.get_other _ index query _ different] at missing
    exact initial.vacant query missing

/-- Real exposeTag retains scalar SIFA/permission profiles and physical Clean;
its actual cache update loop is derived from the present-node depth data. -/
theorem expose_profile (tree : BorrowTree) (protections : ProtectedTags) (index : UniIndex) (node : TreeNode)
    (present : tree.nodeAt index = some node) (tagged : tree.indexOfTag node.tag = some index)
    (depth : ParentDepth tree.nodes)
    (initial : Every (fun location => GeneralBorrowLocationSifaConsistency.Profile tree location protections) tree.locations) :
    (tree.exposeTag protections node.tag).outcome = .ok () ∧
      Every (fun location => GeneralBorrowLocationSifaConsistency.Profile (tree.exposeTag protections node.tag).tree location protections)
        (tree.exposeTag protections node.tag).tree.locations := by
  cases exposed : node.isExposed with
  | true =>
    have actual : tree.exposeTag protections node.tag = ⟨tree,.ok ()⟩ := by
      simp [BorrowTree.exposeTag,tagged,present,exposed]
    rw [actual];exact ⟨rfl,initial⟩
  | false =>
    let marked : BorrowTree := {tree with nodes := tree.nodes.insert index {node with isExposed := true}}
    let update := GeneralBorrowPartitionExposeCardinality.callback tree protections index node
    have shape := GeneralBorrowRootExposureFrame.mark_shape tree index node present
    let markedDepth := GeneralBorrowFreshMetadata.parent_depth tree marked shape depth
    have markedPresent : marked.nodeAt index = some {node with isExposed := true} := GeneralBorrowFreshLocation.get_same tree.nodes index _
    have before : Every (fun location => GeneralBorrowLocationSifaConsistency.Profile marked location protections) marked.locations := by
      intro position valid
      exact mark_profile tree _ protections index node present (initial position valid)
    have each : ∀ location,GeneralBorrowLocationSifaConsistency.Profile marked location protections →
        (update location).2 = .ok () ∧ GeneralBorrowLocationSifaConsistency.Profile marked (update location).1 protections := by
      intro location good
      have cacheSuccess := GeneralBorrowExposure.update_exposure_succeeds location.exposedCache marked.nodes markedDepth index _ markedPresent .None
        (GeneralBorrowExposureCardinality.effective location protections index node)
      refine ⟨?_,GeneralBorrowSifaProtectionProfile.perms marked location (update location).1 protections rfl good⟩
      change (location.exposedCache.updateExposure marked.nodes index .None _).outcome.mapError _ = .ok ()
      rw [cacheSuccess];rfl
    have all := GeneralBorrowLocationUpdateProperty.every marked update
      (fun location => GeneralBorrowLocationSifaConsistency.Profile marked location protections)
      (fun location => GeneralBorrowLocationSifaConsistency.Profile marked location protections) before each
    have nodes := GeneralBorrowLocationUpdateFrame.nodes marked update
    have actual : tree.exposeTag protections node.tag = source_location_update marked update := by
      unfold BorrowTree.exposeTag
      simp only [tagged,present,exposed,Bool.false_eq_true,↓reduceIte,Id.run,pure]
      rfl
    rw [actual]
    refine ⟨all.1,?_⟩
    intro position valid
    exact GeneralBorrowSifaProtectionProfile.nodes marked _ _ protections nodes (all.2 position valid)

/-- Actual leading root Read establishes an earlier held reservation conflict,
then actual protected Default append/SIFA retains it. Every input describes the
initial tree/profile, not a successful Read, constructed tree or final conflict. -/
theorem child_conflict (input : GeneralBorrowFreshMetadataChildMutable.Input) (protections : ProtectedTags)
    (roots : input.tree.roots = #[input.parent]) (parentless : input.parentNode.parent = none)
    (earlier : UniIndex) (earlierNode : TreeNode) (earlierPresent : input.tree.nodeAt earlier = some earlierNode)
    (listed : earlier ∈ input.parentNode.children) (held : protections.contains earlierNode.tag = true)
    (readable : Every (GeneralBorrowProtectedReadRelease.Profile input.tree protections) input.tree.locations)
    (physical : Every (fun location => GeneralBorrowLocationSifaConsistency.Profile input.tree location protections) input.tree.locations)
    (typed : GeneralBorrowDefaultReservationType.TreeTyped input.tree earlier) :
    OwnedOn (At earlier (some (.ReservedFrz true))) input.offset (input.offset+input.len)
      (GeneralBorrowProtectedReadableStage.child input protections).tree.locations := by
  have fits : input.tree.nodes.data.size ≤ 4294967296 := by
    have bound := input.fits;have aligned := input.aligned;omega
  have initial : Every (GeneralBorrowProtectedReadRange.Before input.tree protections input.parent earlier) input.tree.locations := by
    intro position valid
    obtain ⟨forest,data⟩ := readable position valid
    refine ⟨⟨forest,GeneralBorrowProtectedReadPermissionMetadata.valid_anchor input.tree _ protections input.parent input.parentNode input.parentPresent,
      GeneralBorrowProtectedReadPermissionMetadata.compatible_initial input.tree _ protections input.parent data⟩,physical position valid,?_,?_,?_⟩
    · exact (input.tree.locations.entries[position].data.perms.get earlier).getD earlierNode.defaultLocationState
    · simp [BorrowTree.locationStateAt,earlierPresent]
    · cases stored : input.tree.locations.entries[position].data.perms.get earlier with
      | none =>
        simp only [stored,Option.getD_none]
        exact typed.1 earlierNode earlierPresent
      | some state =>
        simp only [stored,Option.getD_some]
        exact typed.2 position valid state stored
  have conflict := GeneralBorrowProtectedReadRange.root_conflict input.tree protections input.parentTag input.parent earlier
    input.parentNode earlierNode input.offset input.len fits input.depth input.children input.covered roots input.parentTagPresent
    input.parentPresent parentless earlierPresent listed held input.well input.bounds initial
  have vacant : input.tree.nodes.get (GeneralBorrowFreshMetadataChildMutable.index input) = none := by
    simp [UniValMap.get,GeneralBorrowFreshMetadataChildMutable.at_end input]
  have clean : Every (fun location : LocationTree => location.perms.get (GeneralBorrowFreshMetadataChildMutable.index input) = none) input.tree.locations := by
    intro position valid;exact (physical position valid).vacant _ vacant
  let prepared := GeneralBorrowProtectedReadableStage.prepare input protections roots readable clean
  have frame := GeneralBorrowFreshReadFrame.frame input.tree (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .Read protections .VisitChildrenOfAccessed
  change (GeneralBorrowProtectedReadableStage.read input protections).tree =
    {input.tree with locations := (GeneralBorrowProtectedReadableStage.read input protections).tree.locations} at frame
  have mapping : prepared.next.tree.tagMapping = input.tree.tagMapping := by rw [prepared.tree,frame]
  have different : earlier ≠ GeneralBorrowFreshMetadataChildMutable.index prepared.next := by
    intro same
    have bound := (GeneralBorrowProjection.array_of_node input.tree earlier earlierNode earlierPresent).1
    have index : GeneralBorrowFreshMetadataChildMutable.index prepared.next = GeneralBorrowFreshMetadataChildMutable.index input := by
      unfold GeneralBorrowFreshMetadataChildMutable.index
      rw [mapping]
    have equal := congrArg UniIndex.toNat (same.trans index)
    rw [GeneralBorrowFreshMetadataChildMutable.at_end input] at equal
    omega
  change (GeneralBorrowProtectedReadableStage.read input protections).status = .Completed ∧
    OwnedOn (At earlier (some (.ReservedFrz true))) input.offset (input.offset+input.len)
      (GeneralBorrowProtectedReadableStage.read input protections).tree.locations at conflict
  have afterRead : OwnedOn (At earlier (some (.ReservedFrz true))) input.offset (input.offset+input.len) prepared.next.tree.locations := by
    rw [prepared.tree];exact conflict.2
  have retained := GeneralBorrowConstructorPriorPermissionRange.protected_append prepared.next earlier (some (.ReservedFrz true))
    input.offset (input.offset+input.len) different afterRead
  rw [prepared.result] at retained
  exact retained.2
end DuplicatePrefix.GeneralBorrowTwoProtectedStateInfoConflict
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowTwoProtectedStateInfoConflict.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved two protected state conflict dependency {dependency}"
