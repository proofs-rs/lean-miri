import duplicate_prefix.GeneralBorrowProtectedReadInvariant
import duplicate_prefix.GeneralBorrowNormalPermissionMetadata
namespace DuplicatePrefix.GeneralBorrowProtectedReadPermissionMetadata
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowEvents
open DuplicatePrefix.GeneralBorrowStorage DuplicatePrefix.GeneralBorrowExposureCardinality
open DuplicatePrefix.GeneralBorrowNormalPermissionMetadataData
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem valid_anchor (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (node : TreeNode) (present : tree.nodeAt anchor = some node) :
    anchor.toNat < (source_normal_projection tree location protections).topology.nodes.size := by
  obtain ⟨bounded,_⟩ := array_of_node tree anchor node present
  unfold_general_projection;unfold_general_topology
  simpa only [Array.size_map] using bounded

theorem projection_aligned (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) :
    (source_normal_projection tree location protections).locationStates.size =
      (source_normal_projection tree location protections).topology.nodes.size := by
  unfold_general_projection;unfold_general_topology
  simp only [Array.size_mapIdx,Array.size_map]

theorem compatible_initial (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) (anchor : UniIndex)
    (initial : GeneralBorrowProtectedReadInvariant.Data (source_normal_projection tree location protections)) :
    ∀ index,index < (source_normal_projection tree location protections).topology.nodes.size → ∃ state,
      (source_normal_projection tree location protections).stateAt index = some state ∧
      GeneralBorrowProtectedReadCompatible.Compatible state
        (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat index)
        ((source_normal_projection tree location protections).protectedNodes.contains index) := by
  intro index bounded
  have aligned := projection_aligned tree location protections
  obtain ⟨state,present,good⟩ := initial index (by omega)
  exact ⟨state,present,GeneralBorrowProtectedReadInvariant.compatible state _ _ good⟩

/-- All physical transition endpoints and visitor uniqueness are derived from
initial readable protected data, including active held foreign reservations. -/
theorem metadata (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (mode : ChildrenVisitMode)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (initial : GeneralBorrowProtectedReadInvariant.Data (source_normal_projection tree location protections))
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode) :
    (((source_normal_projection tree location protections).performAccess anchor.toNat .Read mode).visited.map TraversalEvent.node).Nodup ∧
    ∀ event ∈ ((source_normal_projection tree location protections).performAccess anchor.toNat .Read mode).visited,
      Nonempty (EventMetadata tree location protections anchor .Read mode event) := by
  let projected := source_normal_projection tree location protections
  let schedule := projected.topology.traverse anchor.toNat mode (sourceNormalSkipped projected .Read)
  have valid := valid_anchor tree location protections anchor anchorNode anchorPresent
  have aligned := projection_aligned tree location protections
  have compatible := compatible_initial tree location protections anchor initial
  have scheduleData := GeneralBorrowTraversal.traversal_data projected.topology forest anchor.toNat valid mode (sourceNormalSkipped projected .Read)
  have completed := GeneralBorrowProtectedReadCompatible.normal projected forest anchor.toNat valid mode aligned compatible
  have visited := GeneralBorrowStorage.events_visited schedule.2 schedule.1 .Read projected completed
  change (projected.performAccess anchor.toNat .Read mode).visited = schedule.2 at visited
  refine ⟨?_,?_⟩
  · rw [visited];exact scheduleData.1
  · intro event member
    have scheduled : event ∈ schedule.2 := by rw [←visited];exact member
    obtain ⟨index,node,converted,indexEq,present⟩ := GeneralBorrowGraph.visited_present tree location protections
      depth children anchor anchorNode anchorPresent .Read mode event scheduled
    obtain ⟨endpoint⟩ := GeneralBorrowProtectedReadCompatible.normal_endpoints projected forest anchor.toNat valid mode aligned compatible event scheduled
    have oldPresent : tree.locationStateAt location index = some endpoint.oldState := by
      rw [←projection_location_state tree location protections index node present,indexEq]
      exact endpoint.oldPresent
    have finalStored : (projected.performAccess anchor.toNat .Read mode).tree.locationStates[index.toNat]? = some (some endpoint.newState) := by
      rw [indexEq];exact endpoint.finalStored
    have newPresent : (projected.performAccess anchor.toNat .Read mode).tree.stateAt event.node = some endpoint.newState := by
      change (sourceNormalEvents projected schedule.1 .Read schedule.2).tree.stateAt event.node = _
      have stored : (sourceNormalEvents projected schedule.1 .Read schedule.2).tree.locationStates[event.node]? = some (some endpoint.newState) := endpoint.finalStored
      simp only [NormalTreeState.stateAt,stored]
    have protect : projected.protectedNodes.contains event.node = protections.contains node.tag := by
      rw [←indexEq];exact GeneralBorrowNormalPermissionMetadata.held tree location protections index node present
    have performed : performAccessTransition .Read event.relatedness endpoint.oldState.permission (protections.contains node.tag) = .Transition endpoint.transition := by
      rw [←protect];exact endpoint.performed
    have actualStored := GeneralBorrowNormalStoredWriteback.stored tree location protections anchor index .Read mode endpoint.newState finalStored
    refine ⟨⟨index,node,endpoint.oldState,endpoint.newState,endpoint.transition,converted,present,oldPresent,newPresent,
      performed,endpoint.fromPermission,endpoint.toPermission,finalStored,?_,?_⟩⟩
    · intro noop
      have same : endpoint.transition.fromPermission = endpoint.transition.toPermission := by
        simpa only [PermTransition.isNoop,beq_iff_eq] using noop
      rw [←endpoint.fromPermission,←endpoint.toPermission,same]
    · simp only [effective,actualStored,Option.getD_some]

/-- Unvisited actual present nodes retain their initial effective local access
level through the real normal operation and write-back, including lazy slots. -/
theorem unvisited (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (mode : ChildrenVisitMode)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (initial : GeneralBorrowProtectedReadInvariant.Data (source_normal_projection tree location protections))
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (index : UniIndex) (node : TreeNode) (present : tree.nodeAt index = some node)
    (outside : index.toNat ∉ ((source_normal_projection tree location protections).performAccess anchor.toNat .Read mode).visited.map TraversalEvent.node) :
    effective (tree.performNormalAccessAt location anchor .Read protections mode).location protections index node =
      effective location protections index node := by
  let projected := source_normal_projection tree location protections
  let schedule := projected.topology.traverse anchor.toNat mode (sourceNormalSkipped projected .Read)
  have valid := valid_anchor tree location protections anchor anchorNode anchorPresent
  have aligned := projection_aligned tree location protections
  have compatible := compatible_initial tree location protections anchor initial
  have completed := GeneralBorrowProtectedReadCompatible.normal projected forest anchor.toNat valid mode aligned compatible
  have visited := GeneralBorrowStorage.events_visited schedule.2 schedule.1 .Read projected completed
  change (projected.performAccess anchor.toNat .Read mode).visited = schedule.2 at visited
  have rawOutside : ∀ event ∈ schedule.2, event.node ≠ index.toNat := by
    intro event member equal
    apply outside
    exact List.mem_map.mpr ⟨event,by rw [visited];exact member,equal⟩
  have same := GeneralBorrowTwoRootNormalAccess.normal_unvisited tree location protections anchor index node .Read mode present rawOutside
  simp only [effective,same]

end DuplicatePrefix.GeneralBorrowProtectedReadPermissionMetadata
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedReadPermissionMetadata.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protected Read permission metadata dependency {dependency}"
