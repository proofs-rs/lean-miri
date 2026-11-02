import duplicate_prefix.GeneralBorrowNormalSifaConsistency
import duplicate_prefix.GeneralBorrowNormalPermissionMetadata
import duplicate_prefix.GeneralBorrowTwoRootNormalAccess
namespace DuplicatePrefix.GeneralBorrowLocationSifaConsistency
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowStorage
open DuplicatePrefix.GeneralBorrowSifaPermissionConsistency DuplicatePrefix.GeneralBorrowFreshActiveOnClean
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] UniValMap.insert

/-- Physical permission/SIFA consistency, including clean vacant permission
slots. It is independent of ownership, exposed cache counts and access success. -/
structure Profile (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) : Prop where
  present : ∀ index node,tree.nodeAt index = some node →
    Consistent ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)
  vacant : ∀ index,tree.nodes.get index = none → location.perms.get index = none

/-- Raw per-present-node bounds and clean vacancies form the exact source
normal projection's complete scalar SIFA profile, including lazy defaults. -/
theorem projection (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (fits : tree.nodes.data.size ≤ 4294967296) (initial : Profile tree location protections) :
    GeneralBorrowNormalSifaConsistency.Profile (source_normal_projection tree location protections) := by
  intro position state stored
  have bounded : position < (source_normal_projection tree location protections).locationStates.size := by
    by_cases bounded : position < (source_normal_projection tree location protections).locationStates.size
    · exact bounded
    · have absent : (source_normal_projection tree location protections).locationStates[position]? = none := Array.getElem?_eq_none (by omega)
      simp only [NormalTreeState.stateAt,absent] at stored
      cases stored
  have valid : position < tree.nodes.data.size := by rw [←(projection_sizes tree location protections).1];exact bounded
  obtain ⟨index,converted,indexEq⟩ := index_nat position (by omega)
  cases present : tree.nodeAt index with
  | some node =>
    have actual := projection_state tree location protections position index node converted indexEq present
    have equal : state = (location.perms.get index).getD node.defaultLocationState := Option.some.inj (stored.symm.trans actual)
    subst state
    rw [←indexEq,GeneralBorrowNormalPermissionMetadata.held tree location protections index node present]
    exact initial.present index node present
  | none =>
    have clean := initial.vacant index present
    have slot : tree.nodes.data[position] = none := by
      unfold BorrowTree.nodeAt UniValMap.get at present
      rw [indexEq,Array.getElem?_eq_getElem valid] at present
      exact present
    have actual : (source_normal_projection tree location protections).stateAt position = some ⟨.Disabled,false,.None⟩ := by
      unfold_general_projection
      simp only [NormalTreeState.stateAt,Array.getElem?_mapIdx,Array.getElem?_map,Array.getElem?_eq_getElem valid,
        converted,clean,slot,Option.map_some]
    have equal : state = ⟨.Disabled,false,.None⟩ := Option.some.inj (stored.symm.trans actual)
    subst state
    exact GeneralBorrowSifaPermissionConsistency.vacant _

/-- Actual normal access, materialization and cache scan preserve the physical
SIFA profile on arbitrary finite forests, both access kinds and both visit
modes. Ownership derives real operation completion; no success is a premise. -/
theorem normal (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (kind : AccessKind) (mode : ChildrenVisitMode)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location protections) anchor.toNat kind)
    (initial : Profile tree location protections) :
    (tree.performNormalAccessAt location anchor kind protections mode).access.status = .Completed ∧
    (tree.performNormalAccessAt location anchor kind protections mode).outcome = .ok () ∧
    Profile tree (tree.performNormalAccessAt location anchor kind protections mode).location protections := by
  have complete := GeneralBorrowNormalLocation.normal_succeeds tree location protections anchor kind mode forest owned depth children anchorNode anchorPresent
  have raw := GeneralBorrowNormalSifaConsistency.normal (source_normal_projection tree location protections) forest anchor.toNat kind mode owned
    (projection tree location protections fits initial)
  have metadata := GeneralBorrowNormalPermissionMetadata.metadata tree location protections anchor kind mode forest owned depth children anchorNode anchorPresent
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

end DuplicatePrefix.GeneralBorrowLocationSifaConsistency
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowLocationSifaConsistency.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved physical SIFA consistency dependency {dependency}"
