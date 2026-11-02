import duplicate_prefix.GeneralBorrowCompatibleScopedNormalExposure
import duplicate_prefix.GeneralBorrowWildcardPrimaryReadWitness
namespace DuplicatePrefix.GeneralBorrowCompatibleNormalReadFrame
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowExposure GeneralBorrowExposureCardinality
open GeneralBorrowWildcardPrimaryReadWitness (PointwiseReadFrame)
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

private theorem support_allows (level : WildcardAccessLevel) : supports level .Read = level.allows .Read := by
  cases level <;> rfl

private theorem transition_support (permission : Permission) (related : AccessRelatedness) (held : Bool)
    (transition : PermTransition)
    (unprotected : related = .ForeignAccess → held = true → permission ≠ .Unique)
    (performed : performAccessTransition .Read related permission held = .Transition transition) :
    supports (transition.toPermission.strongestAllowedLocalAccess held) .Read =
      supports (permission.strongestAllowedLocalAccess held) .Read := by
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases related <;> cases held <;>
      first
      | (change PermTransitionOutcome.UndefinedBehavior = .Transition transition at performed; cases performed)
      | (change PermTransitionOutcome.ImpossibleProtectedReservedIM = .Transition transition at performed; cases performed)
      | (change PermTransitionOutcome.Transition _ = .Transition transition at performed; cases performed; first | rfl | exact False.elim (unprotected rfl rfl rfl))
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases related <;> cases held <;>
      first
      | (change PermTransitionOutcome.UndefinedBehavior = .Transition transition at performed; cases performed)
      | (change PermTransitionOutcome.ImpossibleProtectedReservedIM = .Transition transition at performed; cases performed)
      | (change PermTransitionOutcome.Transition _ = .Transition transition at performed; cases performed; first | rfl | exact False.elim (unprotected rfl rfl rfl))

/-- An actual compatible normal Read preserves Read support at every present
node, including nodes outside the selected component and lazy stored rows. -/
theorem pointwise (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (mode : ChildrenVisitMode)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (component : GeneralBorrowExposedScopedNormal.Component (source_normal_projection tree location protections).topology anchor.toNat)
    (owned : GeneralBorrowCompatibleScopedNormal.Owned (source_normal_projection tree location protections) anchor.toNat .Read component)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode) :
    PointwiseReadFrame tree protections location (tree.performNormalAccessAt location anchor .Read protections mode).location := by
  have metadata := GeneralBorrowCompatibleScopedNormalMetadata.metadata tree location protections anchor .Read mode
    forest component owned depth children anchorNode anchorPresent
  let projected := source_normal_projection tree location protections
  have geometry := GeneralBorrowExposedScopedNormalMetadata.valid_aligned tree location protections anchor anchorNode anchorPresent
  have completed := GeneralBorrowCompatibleScopedNormal.normal projected anchor.toNat .Read mode forest geometry.1 geometry.2 component owned
  have visited := GeneralBorrowStorage.events_visited
    (projected.topology.traverse anchor.toNat mode (sourceNormalSkipped projected .Read)).2
    (projected.topology.traverse anchor.toNat mode (sourceNormalSkipped projected .Read)).1 .Read projected completed
  change (projected.performAccess anchor.toNat .Read mode).visited = _ at visited
  have eventsCompatible := GeneralBorrowCompatibleScopedNormalMetadata.schedule_owned projected forest anchor.toNat .Read mode
    geometry.1 geometry.2 component owned
  intro index node present
  change tree.nodeAt index = some node at present
  by_cases included : index.toNat ∈ (((source_normal_projection tree location protections).performAccess anchor.toNat .Read mode).visited.map TraversalEvent.node)
  · obtain ⟨event,member,eventEq⟩ := List.mem_map.mp included
    obtain ⟨data⟩ := metadata.2 event member
    have sameIndex : data.index = index := Option.some.inj (data.converted.symm.trans (by rw [eventEq];exact index_self index))
    have dataPresent : tree.nodeAt index = some data.node := by simpa only [sameIndex] using data.present
    have sameNode : data.node = node := Option.some.inj (dataPresent.symm.trans present)
    have old : effective location protections index node = data.oldState.permission.strongestAllowedLocalAccess (protections.contains node.tag) := by
      have lookup : tree.locationStateAt location index = some data.oldState := by simpa only [sameIndex] using data.oldPresent
      have state : (location.perms.get index).getD node.defaultLocationState = data.oldState := by
        simpa only [BorrowTree.locationStateAt,present,bind,pure,Option.bind_some,Option.some.injEq] using lookup
      simp only [effective,state]
    have newer : effective (tree.performNormalAccessAt location anchor .Read protections mode).location protections index node =
        data.newState.permission.strongestAllowedLocalAccess (protections.contains node.tag) := by
      simpa only [sameIndex,sameNode] using data.newEffective
    have scheduled : event ∈ (projected.topology.traverse anchor.toNat mode (sourceNormalSkipped projected .Read)).2 := by
      rw [←visited]
      exact member
    obtain ⟨state,statePresent,_,compatible,_⟩ := eventsCompatible event scheduled
    have lookup : tree.locationStateAt location index = some data.oldState := by simpa only [sameIndex] using data.oldPresent
    have oldProjected : projected.stateAt event.node = some data.oldState := by
      rw [eventEq]
      exact (projection_location_state tree location protections index node present).trans lookup
    have sameState : state = data.oldState := Option.some.inj (statePresent.symm.trans oldProjected)
    have held := GeneralBorrowNormalPermissionMetadata.held tree location protections index node present
    have unprotected : event.relatedness = .ForeignAccess → (protections.contains node.tag) = true → data.oldState.permission ≠ .Unique := by
      intro foreign heldTrue
      rw [sameState,eventEq,held,foreign] at compatible
      exact (compatible.2 (by exact heldTrue)).1
    have support := transition_support data.oldState.permission event.relatedness (protections.contains node.tag) data.transition unprotected
      (by simpa only [sameNode] using data.performed)
    rw [data.finalEndpoint] at support
    simpa only [←support_allows,newer,old,sameNode] using support
  · have unchanged := GeneralBorrowCompatibleScopedNormalMetadata.unvisited tree location protections anchor .Read mode
      forest component owned anchorNode anchorPresent index node present included
    rw [unchanged]

/-- Coherence and pointwise Read support give equality of the actual finite
Read counters globally; no short-counter bound is needed for this equality. -/
theorem counters (tree : BorrowTree) (before after : LocationTree) (protections : ProtectedTags)
    (oldCoherent : LocationCoherent tree before protections) (newCoherent : LocationCoherent tree after protections)
    (frame : PointwiseReadFrame tree protections before after) : GeneralBorrowExposedNonleafState.ReadFrame before after := by
  intro query
  rw [newCoherent query .Read,oldCoherent query .Read]
  congr 1
  unfold cardinality
  congr 1
  apply List.filter_congr
  intro row member
  have present := (GeneralBorrowFreshReuseProtection.entries_get tree.nodes row.1 row.2).mp member
  have same := frame row.1 row.2 present
  simp only [contributes,support_allows,same]

end DuplicatePrefix.GeneralBorrowCompatibleNormalReadFrame
