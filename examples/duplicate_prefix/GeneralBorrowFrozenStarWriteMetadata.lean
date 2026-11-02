import duplicate_prefix.GeneralBorrowFrozenStarSchedule
import duplicate_prefix.GeneralBorrowWriteCacheFold
import duplicate_prefix.GeneralBorrowStarOwnership

namespace DuplicatePrefix.GeneralBorrowFrozenStarWriteMetadata
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowEvents DuplicatePrefix.GeneralBorrowPermissions DuplicatePrefix.GeneralBorrowGeneratedStarShape
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Exact generated Frozen-star profile supplies every source event's raw
permission and exposed-node metadata, and the precise visited-node list. -/
theorem normal (tree : BorrowTree) (location : LocationTree) (root : UniIndex) (rootNode : TreeNode)
    (star : Star tree root rootNode) (profile : GeneralBorrowSharedGeneratorProfile.Profile tree location root)
    (fits : tree.nodes.size ≤ 4294967296)
    (exposed : ∀ index node, tree.nodeAt index = some node → node.isExposed = true) :
    ((source_normal_projection tree location {}).performAccess root.toNat .Write .VisitChildrenOfAccessed).visited =
      ⟨root.toNat,.LocalAccess⟩ :: rootNode.children.toList.reverse.map (fun index => ⟨index.toNat,.ForeignAccess⟩) ∧
    (∀ event ∈ ((source_normal_projection tree location {}).performAccess root.toNat .Write .VisitChildrenOfAccessed).visited,
      Nonempty (GeneralBorrowWriteCacheFold.EventMetadata tree location root .VisitChildrenOfAccessed event)) := by
  let normal := source_normal_projection tree location {}
  let events := (normal.topology.traverse root.toNat .VisitChildrenOfAccessed (sourceNormalSkipped normal .Write)).2
  obtain ⟨⟨forest⟩,owned⟩ := GeneralBorrowStarOwnership.location_owned tree root rootNode star location profile fits
  have schedule := GeneralBorrowTraversal.traversal_data normal.topology forest root.toNat owned.anchorValid .VisitChildrenOfAccessed (sourceNormalSkipped normal .Write)
  have path := GeneralBorrowFrozenStarSchedule.root_path tree location root rootNode star.present star.parentless
  have pointwise : EventsOwned normal .Write events := by
    intro event member
    have shape := schedule.2 event member
    obtain ⟨state,present,permission⟩ := owned.permissions event.node shape.1
    refine ⟨state,present,?_,?_,?_⟩
    · rw [owned.locationsAligned];exact shape.1
    · rw [shape.2];exact permission
    · apply recurse_scheduled
      cases related : event.relatedness with
      | LocalAccess => rfl
      | ForeignAccess =>
        have unskipped := GeneralBorrowTopology.traversal_foreign_not_skipped normal.topology (sourceNormalSkipped normal .Write)
          root.toNat .VisitChildrenOfAccessed event member related
        have cannotSkip : state.skipIfKnownNoop .Write .ForeignAccess ≠ .SkipSelfAndChildren := by
          intro skip
          exact unskipped ((skipped_iff normal .Write event.node state present shape.1).mpr skip)
        cases skip : state.skipIfKnownNoop .Write .ForeignAccess with
        | Recurse => rfl
        | SkipSelfAndChildren => exact False.elim (cannotSkip skip)
  have done := GeneralBorrowTraversal.normal_access normal forest root.toNat .Write .VisitChildrenOfAccessed owned
  have visited : (normal.performAccess root.toNat .Write .VisitChildrenOfAccessed).visited = events :=
    GeneralBorrowStorage.events_visited events _ .Write normal done
  have exactEvents := GeneralBorrowFrozenStarSchedule.schedule tree location root rootNode star profile
  refine ⟨visited.trans exactEvents,?_⟩
  intro event member
  rw [visited] at member
  obtain ⟨index,node,converted,indexEq,present⟩ := GeneralBorrowGraph.visited_present tree location {}
    (GeneralBorrowStarCertificates.depth tree root rootNode star) (GeneralBorrowStarCertificates.children tree root rootNode star)
    root rootNode star.present .Write .VisitChildrenOfAccessed event member
  have valid := (schedule.2 event member).1
  have related := (schedule.2 event member).2
  rw [path] at related
  by_cases same : index = root
  · subst index
    have eventRelated : event.relatedness = .LocalAccess := by simpa only [←indexEq,List.mem_singleton,ite_true] using related
    have oldPresent : tree.locationStateAt location root = some GeneralBorrowWildcardLeaf.unique := by
      simp only [BorrowTree.locationStateAt,star.present,profile.rootStored,bind,Option.bind_some,Option.getD_some,pure]
    obtain ⟨next,nextPresent⟩ := GeneralBorrowStorage.events_total events _ .Write normal
      (owned.defaultsAligned.trans owned.locationsAligned.symm) event.node (by rw [owned.locationsAligned];exact valid)
    exact ⟨⟨root,node,GeneralBorrowWildcardLeaf.unique,next,converted,present,oldPresent,nextPresent,exposed root node present,
      Or.inl ⟨rfl,rfl,eventRelated⟩⟩⟩
  · have different : event.node ≠ root.toNat := by intro equal;exact same (GeneralBorrowNodeUpdate.index_injective index root (indexEq.trans equal))
    have eventRelated : event.relatedness = .ForeignAccess := by simpa only [List.mem_singleton,ite_eq_right different] using related
    have stored := profile.shared index node present same
    have oldPresent : tree.locationStateAt location index = some GeneralBorrowFreshAnchor.sharedState := by
      simp only [BorrowTree.locationStateAt,present,stored,bind,Option.bind_some,Option.getD_some,pure]
    have effective : normal.stateAt event.node = some GeneralBorrowFreshAnchor.sharedState := by
      dsimp only [normal]
      rw [projection_state tree location {} event.node index node converted indexEq present,stored]
      rfl
    have selected : (⟨event.node,.ForeignAccess⟩ : TraversalEvent) ∈ events := by
      have equal : (⟨event.node,.ForeignAccess⟩ : TraversalEvent) = event := by cases event;cases eventRelated;rfl
      rw [equal];exact member
    have disabled := GeneralBorrowFrozenWriteEvents.events_disable events (normal.topology.traverse root.toNat .VisitChildrenOfAccessed (sourceNormalSkipped normal .Write)).1 event.node normal schedule.1 pointwise selected
      (by intro other inEvents equal;have r := (schedule.2 other inEvents).2;rw [path,equal] at r;simpa only [List.mem_singleton,ite_eq_right different] using r)
      (by dsimp only [normal];unfold_general_projection;simp [ProtectedTags.contains,ProtectedTags.get])
      (by intro state found;have equal := Option.some.inj (effective.symm.trans found);rw [←equal];rfl)
    obtain ⟨next,nextStored,nextDisabled⟩ := disabled
    have nextPresent : (normal.performAccess root.toNat .Write .VisitChildrenOfAccessed).tree.stateAt event.node = some next := by
      have storedExact : (normal.performAccess root.toNat .Write .VisitChildrenOfAccessed).tree.locationStates[event.node]? = some (some next) := nextStored
      simp only [NormalTreeState.stateAt,storedExact]
    exact ⟨⟨index,node,GeneralBorrowFreshAnchor.sharedState,next,converted,present,oldPresent,nextPresent,exposed index node present,
      Or.inr ⟨same,(star.leaves index node present same).1,rfl,nextDisabled,eventRelated⟩⟩⟩

end DuplicatePrefix.GeneralBorrowFrozenStarWriteMetadata
