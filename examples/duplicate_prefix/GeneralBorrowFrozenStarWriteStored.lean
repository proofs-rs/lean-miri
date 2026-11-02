import duplicate_prefix.GeneralBorrowFrozenStarWriteMetadata

namespace DuplicatePrefix.GeneralBorrowFrozenStarWriteStored
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowEvents DuplicatePrefix.GeneralBorrowStorage DuplicatePrefix.GeneralBorrowFreshActiveOnClean
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

def Stored (tree : NormalTreeState) (position : Nat) : Prop :=
  ∃ state, tree.locationStates[position]? = some (some state)

private theorem update_stored (tree : NormalTreeState) (position index : Nat)
    (stored : Stored tree position) (valid : index < tree.locationStates.size) (state : LocationState) :
    Stored {tree with locationStates := tree.locationStates.set index (some state) valid} position := by
  by_cases same : index = position
  · subst index
    exact ⟨state,by simp⟩
  · obtain ⟨old,present⟩ := stored
    exact ⟨old,by simpa only [Array.getElem?_set,ite_eq_right same] using present⟩

/-- Actual source events never turn an already stored slot into a lazy default,
including intermediate error results. No successful-event premise is needed. -/
theorem events_stored (events : List TraversalEvent) (root : Nat) (kind : AccessKind)
    (tree : NormalTreeState) (position : Nat) (stored : Stored tree position) :
    Stored (sourceNormalEvents tree root kind events).tree position := by
  induction events generalizing tree with
  | nil => unfold_normal_events;exact stored
  | cons event rest ih =>
    cases present : tree.stateAt event.node with
    | none => unfold_storage_events;simpa only [present] using stored
    | some state =>
      cases record : state.recordNewAccess kind event.relatedness with
      | DebugAssertion => unfold_storage_events;simpa only [present,record] using stored
      | Recorded recorded =>
        cases access : recorded.performAccess kind event.relatedness (tree.protectedNodes.contains event.node) <;>
          by_cases valid : event.node < tree.locationStates.size
        all_goals unfold_storage_events
        all_goals simp only [present,record,access,valid,↓reduceDIte,LocationState.AccessResult.resultingState]
        all_goals first
          | exact stored
          | exact ih _ (update_stored tree position event.node stored valid _)
          | exact update_stored tree position event.node stored valid _

/-- Every actual nonroot node of the exposed Frozen-star profile is explicitly
stored Disabled after the real root Write. This strengthens stateAt to the
locationStates slot needed for physical permission-map writeback. -/
theorem normal_disabled (tree : BorrowTree) (location : LocationTree) (root : UniIndex) (rootNode : TreeNode)
    (star : GeneralBorrowGeneratedStarShape.Star tree root rootNode)
    (profile : GeneralBorrowSharedGeneratorProfile.Profile tree location root)
    (fits : tree.nodes.size ≤ 4294967296)
    (exposed : ∀ index node, tree.nodeAt index = some node → node.isExposed = true)
    (index : UniIndex) (node : TreeNode) (present : tree.nodeAt index = some node) (different : index ≠ root) :
    ∃ state, ((source_normal_projection tree location {}).performAccess root.toNat .Write .VisitChildrenOfAccessed).tree.locationStates[index.toNat]? = some (some state) ∧
      state.permission = .Disabled := by
  let normal := source_normal_projection tree location {}
  have metadata := GeneralBorrowFrozenStarWriteMetadata.normal tree location root rootNode star profile fits exposed
  have listed := (star.children index).mpr ⟨different,node,present⟩
  have member : (⟨index.toNat,.ForeignAccess⟩ : TraversalEvent) ∈ (normal.performAccess root.toNat .Write .VisitChildrenOfAccessed).visited := by
    rw [metadata.1]
    apply List.mem_cons_of_mem
    exact List.mem_map.mpr ⟨index,List.mem_reverse.mpr listed,rfl⟩
  obtain ⟨data⟩ := metadata.2 _ member
  have sameIndex : data.index = index := by
    exact Option.some.inj (data.converted.symm.trans (index_self index))
  have disabled : data.newState.permission = .Disabled := by
    rcases data.transition with localCase | foreign
    · exact False.elim (different (sameIndex.symm.trans localCase.1))
    · exact foreign.2.2.2.1
  have projected : Stored normal index.toNat := by
    refine ⟨GeneralBorrowFreshAnchor.sharedState,?_⟩
    dsimp only [normal]
    unfold_general_projection
    rw [Array.getElem?_mapIdx]
    obtain ⟨valid,nodeStored⟩ := array_of_node tree index node present
    simp only [Array.getElem?_eq_getElem valid,nodeStored,Option.map_some,index_self,profile.shared index node present different]
  have final := events_stored
    (normal.topology.traverse root.toNat .VisitChildrenOfAccessed (sourceNormalSkipped normal .Write)).2
    (normal.topology.traverse root.toNat .VisitChildrenOfAccessed (sourceNormalSkipped normal .Write)).1
    .Write normal index.toNat projected
  change Stored (normal.performAccess root.toNat .Write .VisitChildrenOfAccessed).tree index.toNat at final
  obtain ⟨state,stored⟩ := final
  have exactState : state = data.newState := by
    have exactPresent : (normal.performAccess root.toNat .Write .VisitChildrenOfAccessed).tree.stateAt index.toNat = some data.newState := data.newPresent
    simpa only [NormalTreeState.stateAt,stored,Option.some.injEq] using exactPresent
  refine ⟨state,stored,?_⟩
  rw [exactState]
  exact disabled

end DuplicatePrefix.GeneralBorrowFrozenStarWriteStored
