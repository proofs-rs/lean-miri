import duplicate_prefix.GeneralBorrowCompatibleNormalSifaConsistency
import duplicate_prefix.GeneralBorrowLocationSifaConsistency
import duplicate_prefix.GeneralBorrowStructuralHistorySifaState
namespace DuplicatePrefix.GeneralBorrowCompatibleLocationSifaConsistency
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowExposure GeneralBorrowStorage GeneralBorrowFreshActiveOnClean
open GeneralBorrowLocationSifaConsistency (Profile projection)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Actual normal access, materialization and cache scan preserve the physical
SIFA profile on arbitrary finite forests, both access kinds and both visit
modes. Ownership derives real operation completion; no success is a premise. -/
theorem normal (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (kind : AccessKind) (mode : ChildrenVisitMode)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (component : GeneralBorrowExposedScopedNormal.Component (source_normal_projection tree location protections).topology anchor.toNat)
    (owned : GeneralBorrowCompatibleScopedNormal.Owned (source_normal_projection tree location protections) anchor.toNat kind component)
    (initial : Profile tree location protections) :
    (tree.performNormalAccessAt location anchor kind protections mode).access.status = .Completed ∧
    (tree.performNormalAccessAt location anchor kind protections mode).outcome = .ok () ∧
    Profile tree (tree.performNormalAccessAt location anchor kind protections mode).location protections := by
  have geometry := GeneralBorrowExposedScopedNormalMetadata.valid_aligned tree location protections anchor anchorNode anchorPresent
  have complete := GeneralBorrowCompatibleScopedNormal.access tree location protections anchor kind mode forest component owned depth children anchorNode anchorPresent
  have raw := GeneralBorrowCompatibleNormalSifaConsistency.normal (source_normal_projection tree location protections) forest anchor.toNat kind mode geometry.1 geometry.2 component owned
    (projection tree location protections fits initial)
  have metadata := GeneralBorrowCompatibleScopedNormalMetadata.metadata tree location protections anchor kind mode forest component owned depth children anchorNode anchorPresent
  have visited := GeneralBorrowStorage.events_visited
    ((source_normal_projection tree location protections).topology.traverse anchor.toNat mode (sourceNormalSkipped (source_normal_projection tree location protections) kind)).2
    ((source_normal_projection tree location protections).topology.traverse anchor.toNat mode (sourceNormalSkipped (source_normal_projection tree location protections) kind)).1
    kind (source_normal_projection tree location protections) complete.1
  change ((source_normal_projection tree location protections).performAccess anchor.toNat kind mode).visited = _ at visited
  have storage := GeneralBorrowStorage.events_storage
    ((source_normal_projection tree location protections).topology.traverse anchor.toNat mode (sourceNormalSkipped (source_normal_projection tree location protections) kind)).2
    ((source_normal_projection tree location protections).topology.traverse anchor.toNat mode (sourceNormalSkipped (source_normal_projection tree location protections) kind)).1
    kind (source_normal_projection tree location protections)
  change SameStorage (source_normal_projection tree location protections)
    ((source_normal_projection tree location protections).performAccess anchor.toNat kind mode).tree at storage
  refine ⟨complete.1,complete.2,?_,?_⟩
  · intro query node present
    by_cases member : query.toNat ∈ (((source_normal_projection tree location protections).performAccess anchor.toNat kind mode).visited.map TraversalEvent.node)
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
      have stored := GeneralBorrowNormalStoredWriteback.stored tree location protections anchor facts.index kind mode facts.newState facts.finalStored
      rw [indexEq] at stored
      simpa only [stored,Option.getD_some] using consistent
    · have outside : ∀ event ∈ ((source_normal_projection tree location protections).topology.traverse anchor.toNat mode
          (sourceNormalSkipped (source_normal_projection tree location protections) kind)).2,event.node ≠ query.toNat := by
        intro event scheduled same
        apply member
        exact List.mem_map.mpr ⟨event,by rw [visited];exact scheduled,same⟩
      rw [GeneralBorrowTwoRootNormalAccess.normal_unvisited tree location protections anchor query node kind mode present outside]
      exact initial.present query node present
  · intro query missing
    exact GeneralBorrowFreshActiveOnClean.normal_vacant tree location protections anchor query kind mode depth children anchorNode anchorPresent missing
      (initial.vacant query missing)

private theorem profile_locations (tree : BorrowTree) (locations : DedupRangeMap LocationTree)
    (location : LocationTree) (protections : ProtectedTags) (initial : Profile tree location protections) :
    Profile {tree with locations := locations} location protections :=
  ⟨initial.present, initial.vacant⟩

/-- Store one actual compatible normal result back into its real partition.
The complete structural/allocator/SIFA Formed invariant and every vacant-slot
Clean fact are reconstructed. The generic normal_vacant theorem supplies
vacancy preservation; no append-only/free-pool/profile restriction is added.
Exposure coherence and whole RuntimeFacts reconstruction are separate results. -/
theorem formed_after_row (tree : BorrowTree) (protections : ProtectedTags)
    (initial : GeneralBorrowStructuralHistorySifaState.Formed tree protections)
    (position : Nat) (valid : position < tree.locations.entries.size)
    (anchor : UniIndex) (anchorNode : TreeNode) (present : tree.nodeAt anchor = some anchorNode)
    (kind : AccessKind) (mode : ChildrenVisitMode)
    (component : GeneralBorrowExposedScopedNormal.Component
      (source_normal_projection tree tree.locations.entries[position].data protections).topology anchor.toNat)
    (owned : GeneralBorrowCompatibleScopedNormal.Owned
      (source_normal_projection tree tree.locations.entries[position].data protections) anchor.toNat kind component) :
    let location := tree.locations.entries[position].data
    let result := tree.performNormalAccessAt location anchor kind protections mode
    let after := {tree with locations := GeneralRangeMapState.replaced tree.locations position valid result.location}
    result.access.status = .Completed ∧ result.outcome = .ok () ∧
    GeneralBorrowStructuralHistorySifaState.Formed after protections ∧ GeneralBorrowGcVacantClean.VacantClean after := by
  let location := tree.locations.entries[position].data
  let result := tree.performNormalAccessAt location anchor kind protections mode
  let locations := GeneralRangeMapState.replaced tree.locations position valid result.location
  let after := {tree with locations := locations}
  obtain ⟨forest⟩ := initial.forest location protections
  obtain ⟨depth⟩ := initial.depth
  have accessed := normal tree location protections anchor kind mode initial.fits depth initial.children anchorNode present
    forest component owned (initial.profile position valid)
  have allBefore : GeneralRangeMapState.Every (fun row => Profile after row protections) tree.locations := by
    intro index bounded
    exact profile_locations tree locations _ protections (initial.profile index bounded)
  have newProfile : Profile after result.location protections :=
    profile_locations tree locations _ protections accessed.2.2
  have allAfter : GeneralRangeMapState.Every (fun row => Profile after row protections) locations :=
    GeneralRangeMapState.replaced_every _ tree.locations position valid result.location allBefore newProfile
  have formed : GeneralBorrowStructuralHistorySifaState.Formed after protections :=
    ⟨⟨GeneralBorrowStructuralHistoryState.graph_locations tree locations initial.toGraphState,
      GeneralRangeMapState.replaced_wellFormed tree.locations position valid result.location initial.well⟩, allAfter⟩
  exact ⟨accessed.1, accessed.2.1, formed,
    GeneralBorrowStructuralHistorySifaState.vacant_clean after protections formed⟩

end DuplicatePrefix.GeneralBorrowCompatibleLocationSifaConsistency
