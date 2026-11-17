import duplicate_prefix.GeneralBorrowNormalPermissionMetadata
import duplicate_prefix.GeneralBorrowExposedScopedNormal
import duplicate_prefix.GeneralBorrowEventTransitionMetadata
import duplicate_prefix.GeneralBorrowNormalStoredWriteback
import duplicate_prefix.GeneralBorrowTwoRootNormalAccess
namespace DuplicatePrefix.GeneralBorrowExposedScopedNormalMetadata
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowEvents
open DuplicatePrefix.GeneralBorrowStorage DuplicatePrefix.GeneralBorrowExposureCardinality
open DuplicatePrefix.GeneralBorrowNormalPermissionMetadataData
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000


theorem valid_aligned (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (node : TreeNode) (present : tree.nodeAt anchor = some node) :
    anchor.toNat < (source_normal_projection tree location protections).topology.nodes.size ∧
    (source_normal_projection tree location protections).locationStates.size =
      (source_normal_projection tree location protections).topology.nodes.size := by
  have bounded := GeneralBorrowNodeUpdate.lookup_valid tree.nodes anchor node present
  have topologySize : (source_normal_projection tree location protections).topology.nodes.size = tree.nodes.data.size := by
    unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
  have sizes := projection_sizes tree location protections
  exact ⟨by rw [topologySize];exact bounded,sizes.1.trans topologySize.symm⟩

/-- Ownership supplies every actual scheduled event's initial state, legality
and SIFA recursion condition; no successful-operation premise is supplied. -/
theorem schedule_owned (tree : NormalTreeState) (forest : GeneralBorrowForest.Forest tree.topology)
    (anchor : Nat) (kind : AccessKind) (mode : ChildrenVisitMode)
    (valid : anchor < tree.topology.nodes.size) (aligned : tree.locationStates.size = tree.topology.nodes.size)
    (component : GeneralBorrowExposedScopedNormal.Component tree.topology anchor)
    (owned : GeneralBorrowExposedScopedNormal.Owned tree anchor kind component) :
    EventsOwned tree kind (tree.topology.traverse anchor mode (sourceNormalSkipped tree kind)).2 := by
  have schedule := GeneralBorrowTraversal.traversal_data tree.topology forest anchor valid mode (sourceNormalSkipped tree kind)
  have confined := GeneralBorrowPresence.traversal_present tree.topology component.support component.parents component.children
    anchor component.anchor mode (sourceNormalSkipped tree kind)
  intro event member
  have shape := schedule.2 event member
  obtain ⟨state,present,permission⟩ := owned event.node (confined event member) shape.1
  refine ⟨state,present,?_,?_,?_⟩
  · rw [aligned];exact shape.1
  · rw [shape.2];exact permission
  · apply recurse_scheduled
    cases related : event.relatedness with
    | LocalAccess => rfl
    | ForeignAccess =>
      have unskipped := GeneralBorrowTopology.traversal_foreign_not_skipped tree.topology (sourceNormalSkipped tree kind)
        anchor mode event member related
      have cannotSkip : state.skipIfKnownNoop kind .ForeignAccess ≠ .SkipSelfAndChildren := by
        intro skip
        exact unskipped ((skipped_iff tree kind event.node state present shape.1).mpr skip)
      cases skip : state.skipIfKnownNoop kind .ForeignAccess with
      | Recurse => rfl
      | SkipSelfAndChildren => exact False.elim (cannotSkip skip)

/-- Derive exact permission-transition metadata for every real visitor of an
arbitrary finite normal forest, including effective lazy states and final
materialized write-back. Completion and unique visitation follow from initial
forest/anchor ownership, rather than being input assumptions. -/
theorem metadata (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (kind : AccessKind) (mode : ChildrenVisitMode)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (component : GeneralBorrowExposedScopedNormal.Component (source_normal_projection tree location protections).topology anchor.toNat)
    (owned : GeneralBorrowExposedScopedNormal.Owned (source_normal_projection tree location protections) anchor.toNat kind component)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode) :
    (((source_normal_projection tree location protections).performAccess anchor.toNat kind mode).visited.map TraversalEvent.node).Nodup ∧
    ∀ event ∈ ((source_normal_projection tree location protections).performAccess anchor.toNat kind mode).visited,
      Nonempty (EventMetadata tree location protections anchor kind mode event) := by
  let projected := source_normal_projection tree location protections
  have geometry := valid_aligned tree location protections anchor anchorNode anchorPresent
  have valid := geometry.1
  have aligned := geometry.2
  let schedule := projected.topology.traverse anchor.toNat mode (sourceNormalSkipped projected kind)
  have scheduleData := GeneralBorrowTraversal.traversal_data projected.topology forest anchor.toNat valid mode (sourceNormalSkipped projected kind)
  have pointwise := schedule_owned projected forest anchor.toNat kind mode valid aligned component owned
  have completed := GeneralBorrowExposedScopedNormal.normal projected anchor.toNat kind mode forest valid aligned component owned
  have visited := GeneralBorrowStorage.events_visited schedule.2 schedule.1 kind projected completed
  change (projected.performAccess anchor.toNat kind mode).visited = schedule.2 at visited
  refine ⟨?_,?_⟩
  · rw [visited];exact scheduleData.1
  · intro event member
    have scheduled : event ∈ schedule.2 := by rw [←visited];exact member
    obtain ⟨index,node,converted,indexEq,present⟩ := GeneralBorrowGraph.visited_present tree location protections
      depth children anchor anchorNode anchorPresent kind mode event scheduled
    obtain ⟨endpoint⟩ := GeneralBorrowEventTransitionMetadata.events schedule.2 schedule.1 kind projected scheduleData.1 pointwise event scheduled
    have oldPresent : tree.locationStateAt location index = some endpoint.oldState := by
      rw [←projection_location_state tree location protections index node present,indexEq]
      exact endpoint.oldPresent
    have finalStored : (projected.performAccess anchor.toNat kind mode).tree.locationStates[index.toNat]? = some (some endpoint.newState) := by
      rw [indexEq];exact endpoint.finalStored
    have newPresent : (projected.performAccess anchor.toNat kind mode).tree.stateAt event.node = some endpoint.newState := by
      change (sourceNormalEvents projected schedule.1 kind schedule.2).tree.stateAt event.node = _
      simp only [NormalTreeState.stateAt,endpoint.finalStored]
    have protect : projected.protectedNodes.contains event.node = protections.contains node.tag := by
      rw [←indexEq];exact GeneralBorrowNormalPermissionMetadata.held tree location protections index node present
    have performed : performAccessTransition kind event.relatedness endpoint.oldState.permission (protections.contains node.tag) = .Transition endpoint.transition := by
      rw [←protect];exact endpoint.performed
    have actualStored := GeneralBorrowNormalStoredWriteback.stored tree location protections anchor index kind mode endpoint.newState finalStored
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
    (anchor : UniIndex) (kind : AccessKind) (mode : ChildrenVisitMode)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (component : GeneralBorrowExposedScopedNormal.Component (source_normal_projection tree location protections).topology anchor.toNat)
    (owned : GeneralBorrowExposedScopedNormal.Owned (source_normal_projection tree location protections) anchor.toNat kind component)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (index : UniIndex) (node : TreeNode) (present : tree.nodeAt index = some node)
    (outside : index.toNat ∉ ((source_normal_projection tree location protections).performAccess anchor.toNat kind mode).visited.map TraversalEvent.node) :
    effective (tree.performNormalAccessAt location anchor kind protections mode).location protections index node =
      effective location protections index node := by
  let projected := source_normal_projection tree location protections
  have geometry := valid_aligned tree location protections anchor anchorNode anchorPresent
  have valid := geometry.1
  have aligned := geometry.2
  let schedule := projected.topology.traverse anchor.toNat mode (sourceNormalSkipped projected kind)
  have completed := GeneralBorrowExposedScopedNormal.normal projected anchor.toNat kind mode forest valid aligned component owned
  have visited := GeneralBorrowStorage.events_visited schedule.2 schedule.1 kind projected completed
  change (projected.performAccess anchor.toNat kind mode).visited = schedule.2 at visited
  have rawOutside : ∀ event ∈ schedule.2, event.node ≠ index.toNat := by
    intro event member equal
    apply outside
    exact List.mem_map.mpr ⟨event,by rw [visited];exact member,equal⟩
  have same := GeneralBorrowTwoRootNormalAccess.normal_unvisited tree location protections anchor index node kind mode present rawOutside
  simp only [effective,same]

end DuplicatePrefix.GeneralBorrowExposedScopedNormalMetadata
