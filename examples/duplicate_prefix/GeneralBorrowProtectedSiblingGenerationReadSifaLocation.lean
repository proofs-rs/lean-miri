import duplicate_prefix.GeneralBorrowProtectedSiblingGenerationReadSifa
import duplicate_prefix.GeneralBorrowProtectedReadExposureCache
import duplicate_prefix.GeneralBorrowLocationSifaConsistency
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationReadSifaLocation
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowExposure GeneralBorrowStorage GeneralBorrowFreshActiveOnClean
open GeneralBorrowLocationSifaConsistency
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (mode : ChildrenVisitMode)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (readable : GeneralBorrowProtectedReadInvariant.Data (source_normal_projection tree location protections))
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (initial : Profile tree location protections) :
    (tree.performNormalAccessAt location anchor .Read protections mode).access.status = .Completed ∧
    (tree.performNormalAccessAt location anchor .Read protections mode).outcome = .ok () ∧
    Profile tree (tree.performNormalAccessAt location anchor .Read protections mode).location protections := by
  have valid := GeneralBorrowProtectedReadPermissionMetadata.valid_anchor tree location protections anchor anchorNode anchorPresent
  have complete := GeneralBorrowProtectedReadExposureCache.access tree location protections anchor mode depth children anchorNode anchorPresent forest readable coherent
  have raw := GeneralBorrowProtectedSiblingGenerationReadSifa.normal (source_normal_projection tree location protections) forest anchor.toNat valid mode
    (GeneralBorrowProtectedReadPermissionMetadata.projection_aligned tree location protections) readable
    (projection tree location protections fits initial)
  have metadata := GeneralBorrowProtectedReadPermissionMetadata.metadata tree location protections anchor mode forest readable depth children anchorNode anchorPresent
  have visited := GeneralBorrowStorage.events_visited
    ((source_normal_projection tree location protections).topology.traverse anchor.toNat mode (sourceNormalSkipped (source_normal_projection tree location protections) .Read)).2
    ((source_normal_projection tree location protections).topology.traverse anchor.toNat mode (sourceNormalSkipped (source_normal_projection tree location protections) .Read)).1
    .Read (source_normal_projection tree location protections) complete.1
  change ((source_normal_projection tree location protections).performAccess anchor.toNat .Read mode).visited = _ at visited
  have storage := GeneralBorrowStorage.events_storage
    ((source_normal_projection tree location protections).topology.traverse anchor.toNat mode (sourceNormalSkipped (source_normal_projection tree location protections) .Read)).2
    ((source_normal_projection tree location protections).topology.traverse anchor.toNat mode (sourceNormalSkipped (source_normal_projection tree location protections) .Read)).1
    .Read (source_normal_projection tree location protections)
  change SameStorage (source_normal_projection tree location protections)
    ((source_normal_projection tree location protections).performAccess anchor.toNat .Read mode).tree at storage
  refine ⟨complete.1,complete.2.1,?_,?_⟩
  · intro query node present
    by_cases member : query.toNat ∈ (((source_normal_projection tree location protections).performAccess anchor.toNat .Read mode).visited.map TraversalEvent.node)
    · obtain ⟨event,scheduled,position⟩ := List.mem_map.mp member
      obtain ⟨facts⟩ := metadata.2 event scheduled
      have indexEq : facts.index = query := by
        have converted := facts.converted
        rw [position] at converted
        exact Option.some.inj (converted.symm.trans (index_self query))
      have found := facts.newPresent
      rw [position] at found
      have consistent := raw.2 query.toNat facts.newState found
      rw [storage.2.2.1,GeneralBorrowNormalPermissionMetadata.held tree location protections query node present] at consistent
      have stored := GeneralBorrowNormalStoredWriteback.stored tree location protections anchor facts.index .Read mode facts.newState facts.finalStored
      rw [indexEq] at stored
      simpa only [stored,Option.getD_some] using consistent
    · have outside : ∀ event ∈ ((source_normal_projection tree location protections).topology.traverse anchor.toNat mode
          (sourceNormalSkipped (source_normal_projection tree location protections) .Read)).2,event.node ≠ query.toNat := by
        intro event scheduled same
        apply member
        exact List.mem_map.mpr ⟨event,by rw [visited];exact scheduled,same⟩
      rw [GeneralBorrowTwoRootNormalAccess.normal_unvisited tree location protections anchor query node .Read mode present outside]
      exact initial.present query node present
  · intro query missing
    exact GeneralBorrowFreshActiveOnClean.normal_vacant tree location protections anchor query .Read mode depth children anchorNode anchorPresent missing
      (initial.vacant query missing)

end DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationReadSifaLocation
