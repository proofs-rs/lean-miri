import duplicate_prefix.GeneralBorrowNormalPermissionMetadata
import duplicate_prefix.GeneralBorrowNormalLocation
import duplicate_prefix.GeneralBorrowProtectorCacheMap
namespace DuplicatePrefix.GeneralBorrowProtectedReadProfile
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowExposureCardinality
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] UniValMap.insert

/-- A real constructor-leading normal Read conflicts an earlier protected
reservation on every statically scheduled foreign event for that node. Actual
completion, visitor metadata and stored writeback are derived from initial
forest/ownership. Scheduling is a raw topology/SIFA premise, not access success;
skipped-node profile formation remains separate. -/
theorem foreign_reservation (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor earlier : UniIndex) (anchorNode earlierNode : TreeNode) (state : LocationState) (conflicted : Bool)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorPresent : tree.nodeAt anchor = some anchorNode) (earlierPresent : tree.nodeAt earlier = some earlierNode)
    (oldPresent : tree.locationStateAt location earlier = some state) (reservation : state.permission = .ReservedFrz conflicted)
    (held : protections.contains earlierNode.tag = true)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location protections) anchor.toNat .Read)
    (scheduled : (⟨earlier.toNat,.ForeignAccess⟩ : TraversalEvent) ∈
      ((source_normal_projection tree location protections).topology.traverse anchor.toNat .VisitChildrenOfAccessed
        (sourceNormalSkipped (source_normal_projection tree location protections) .Read)).2) :
    (tree.performNormalAccessAt location anchor .Read protections .VisitChildrenOfAccessed).access.status = .Completed ∧
    (tree.performNormalAccessAt location anchor .Read protections .VisitChildrenOfAccessed).outcome = .ok () ∧
    ∃ next,(tree.performNormalAccessAt location anchor .Read protections .VisitChildrenOfAccessed).location.perms.get earlier = some next ∧
      next.permission = .ReservedFrz true := by
  have complete := GeneralBorrowNormalLocation.normal_succeeds tree location protections anchor .Read .VisitChildrenOfAccessed
    forest owned depth children anchorNode anchorPresent
  have metadata := GeneralBorrowNormalPermissionMetadata.metadata tree location protections anchor .Read .VisitChildrenOfAccessed
    forest owned depth children anchorNode anchorPresent
  have visited := GeneralBorrowStorage.events_visited
    ((source_normal_projection tree location protections).topology.traverse anchor.toNat .VisitChildrenOfAccessed
      (sourceNormalSkipped (source_normal_projection tree location protections) .Read)).2
    ((source_normal_projection tree location protections).topology.traverse anchor.toNat .VisitChildrenOfAccessed
      (sourceNormalSkipped (source_normal_projection tree location protections) .Read)).1
    .Read (source_normal_projection tree location protections) complete.1
  change ((source_normal_projection tree location protections).performAccess anchor.toNat .Read .VisitChildrenOfAccessed).visited = _ at visited
  have member : (⟨earlier.toNat,.ForeignAccess⟩ : TraversalEvent) ∈
      ((source_normal_projection tree location protections).performAccess anchor.toNat .Read .VisitChildrenOfAccessed).visited := by
    rw [visited];exact scheduled
  obtain ⟨facts⟩ := metadata.2 _ member
  have indexEq : facts.index = earlier := by
    exact Option.some.inj (facts.converted.symm.trans (index_self earlier))
  have old : facts.oldState = state := by
    have lookup := facts.oldPresent
    rw [indexEq,oldPresent] at lookup
    exact (Option.some.inj lookup).symm
  have nodeEq : facts.node = earlierNode := by
    have lookup := facts.present
    rw [indexEq,earlierPresent] at lookup
    exact (Option.some.inj lookup).symm
  have performed := facts.performed
  simp only [old,nodeEq,reservation,held] at performed
  have expected : performAccessTransition .Read .ForeignAccess (.ReservedFrz conflicted) true =
      .Transition ⟨.ReservedFrz conflicted,.ReservedFrz true⟩ := by cases conflicted <;> rfl
  have transitionEq : facts.transition = ⟨.ReservedFrz conflicted,.ReservedFrz true⟩ :=
    PermTransitionOutcome.Transition.inj (performed.symm.trans expected)
  have endpoint := facts.finalEndpoint
  rw [transitionEq] at endpoint
  have stored := GeneralBorrowNormalStoredWriteback.stored tree location protections anchor facts.index .Read
    .VisitChildrenOfAccessed facts.newState facts.finalStored
  rw [indexEq] at stored
  exact ⟨complete.1,complete.2,facts.newState,stored,endpoint.symm⟩

/-- Real global/frame registration appends protectors in chronological order.
The release iterator consumes this same array in source order. -/
theorem two_registrations (global : GlobalState) (frame : FrameState)
    (firstAlloc secondAlloc : AllocId) (firstTag secondTag : BorTag)
    (firstKind secondKind : ProtectorKind) :
    let first := global.addProtector frame firstAlloc firstTag firstKind
    let second := first.1.addProtector first.2 secondAlloc secondTag secondKind
    second.2.protectedTags = (frame.protectedTags.push (firstAlloc,firstTag)).push (secondAlloc,secondTag) ∧
    second.2.protectedTags[frame.protectedTags.size]? = some (firstAlloc,firstTag) ∧
    second.2.protectedTags[frame.protectedTags.size+1]? = some (secondAlloc,secondTag) := by
  simp [GlobalState.addProtector,FrameState.addProtector,Array.getElem?_push,Array.getElem_push]

/-- Distinct later registration retains the earlier tag's actual protection,
without requiring the initial global table or frame to be empty. -/
theorem earlier_held (global : GlobalState) (frame : FrameState)
    (firstAlloc secondAlloc : AllocId) (firstTag secondTag : BorTag)
    (firstKind secondKind : ProtectorKind) (different : firstTag ≠ secondTag) :
    let first := global.addProtector frame firstAlloc firstTag firstKind
    let second := first.1.addProtector first.2 secondAlloc secondTag secondKind
    second.1.protectedTags.contains firstTag = true := by
  dsimp only [GlobalState.addProtector]
  simp only [ProtectedTags.contains,GeneralBorrowProtectorCacheMap.insert_other _ secondTag firstTag secondKind different,
    ProtectedTags.get_insert_same,Option.isSome_some]

end DuplicatePrefix.GeneralBorrowProtectedReadProfile
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedReadProfile.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved chronological protected Read profile dependency {dependency}"
