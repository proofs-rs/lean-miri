import duplicate_prefix.GeneralBorrowExposedScopedAncestorNormal
namespace DuplicatePrefix.GeneralBorrowExposedScopedAncestorPermission
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowExposure
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Actual normal Read/Write preserves the raw exposed-ancestor Unique profile.
The claim concerns actual final effective states, including lazy state slots;
it is derived from initial scoped ownership and actual visitor metadata. -/
theorem preserves (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (kind : AccessKind) (mode : ChildrenVisitMode)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (component : GeneralBorrowExposedScopedNormal.Component (source_normal_projection tree location protections).topology anchor.toNat)
    (owned : GeneralBorrowExposedScopedNormal.Owned (source_normal_projection tree location protections) anchor.toNat kind component)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (profile : ∀ index node state,component.support index.toNat → tree.nodeAt index = some node →
      node.isExposed = true → tree.locationStateAt location index = some state →
      index.toNat ∈ (source_normal_projection tree location protections).topology.ancestorPath anchor.toNat ∧
      state.permission = .Unique) :
    ∀ index node state,component.support index.toNat → tree.nodeAt index = some node →
      node.isExposed = true → tree.locationStateAt (tree.performNormalAccessAt location anchor kind protections mode).location index = some state →
      index.toNat ∈ (source_normal_projection tree location protections).topology.ancestorPath anchor.toNat ∧ state.permission = .Unique := by
  let projection := source_normal_projection tree location protections
  let schedule := projection.topology.traverse anchor.toNat mode (sourceNormalSkipped projection kind)
  have geometry := GeneralBorrowExposedScopedNormalMetadata.valid_aligned tree location protections anchor anchorNode anchorPresent
  have completed := GeneralBorrowExposedScopedNormal.normal projection anchor.toNat kind mode forest geometry.1 geometry.2 component owned
  have visited := GeneralBorrowStorage.events_visited schedule.2 schedule.1 kind projection completed
  change (projection.performAccess anchor.toNat kind mode).visited = schedule.2 at visited
  have metadata := GeneralBorrowExposedScopedNormalMetadata.metadata tree location protections anchor kind mode
    forest component owned depth children anchorNode anchorPresent
  intro index node state inside present exposed finalPresent
  by_cases occurs : ∃ event ∈ (projection.performAccess anchor.toNat kind mode).visited,event.node = index.toNat
  · obtain ⟨event,member,same⟩ := occurs
    obtain ⟨facts⟩ := metadata.2 event member
    have indexEq : facts.index=index := by
      apply Option.some.inj
      rw [←facts.converted,same,index_self]
    have oldPresent : tree.locationStateAt location index = some facts.oldState := by rw [←indexEq];exact facts.oldPresent
    obtain ⟨ancestor,unique⟩ := profile index node facts.oldState inside present exposed oldPresent
    have scheduled : event ∈ schedule.2 := by rw [←visited];exact member
    have relation := (GeneralBorrowTraversal.traversal_data projection.topology forest anchor.toNat geometry.1 mode
      (sourceNormalSkipped projection kind)).2 event scheduled
    have localEvent : event.relatedness = .LocalAccess := by
      change index.toNat ∈ projection.topology.ancestorPath anchor.toNat at ancestor
      simpa only [same,ite_eq_left ancestor] using relation.2
    have transition := facts.performed
    rw [localEvent,unique,GeneralBorrowRootOnlyNormalCache.unique_local_noop] at transition
    have transitionEq : facts.transition = ⟨.Unique,.Unique⟩ := (PermTransitionOutcome.Transition.inj transition).symm
    have finalUnique : facts.newState.permission = .Unique := by rw [←facts.finalEndpoint,transitionEq]
    have stored := GeneralBorrowNormalStoredWriteback.stored tree location protections anchor facts.index kind mode facts.newState facts.finalStored
    rw [indexEq] at stored
    have stateEq : state = facts.newState := by
      simpa only [BorrowTree.locationStateAt,present,bind,pure,Option.bind_some,stored,Option.getD_some,Option.some.injEq] using finalPresent.symm
    exact ⟨ancestor,stateEq ▸ finalUnique⟩
  · have outside : ∀ event ∈ schedule.2,event.node ≠ index.toNat := by
      intro event member same
      exact occurs ⟨event,by rw [visited];exact member,same⟩
    have stored := GeneralBorrowTwoRootNormalAccess.normal_unvisited tree location protections anchor index node kind mode present outside
    have oldPresent : tree.locationStateAt location index = some state := by
      simpa only [BorrowTree.locationStateAt,present,bind,pure,Option.bind_some,stored] using finalPresent
    exact profile index node state inside present exposed oldPresent
end DuplicatePrefix.GeneralBorrowExposedScopedAncestorPermission
