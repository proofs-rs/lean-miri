import duplicate_prefix.GeneralBorrowRangePreserves

namespace DuplicatePrefix.GeneralBorrowUnprotectedReadOther
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowPermissions DuplicatePrefix.GeneralBorrowOwnership DuplicatePrefix.GeneralBorrowEvents
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.BorrowRangeAccess
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Unprotected Read preserves every old Read contract, even when the actual
source and owner have different relatedness to this state. -/
theorem state_preserves (state : LocationState) (actual owner : AccessRelatedness)
    (owned : AccessOwned state .Read owner false) :
    AccessOwned (state.performAccess .Read actual false).resultingState .Read owner false := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases accessed <;> cases sifa <;> cases actual <;> cases owner <;>
      simp [AccessOwned,Owned,LocalReadable,ForeignOwned,LocationState.possible,Permission.isUnique] at owned <;> simp only [AccessOwned,Owned,LocalReadable,ForeignOwned] <;> decide
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases accessed <;> cases sifa <;> cases actual <;> cases owner <;>
      simp [AccessOwned,Owned,LocalReadable,ForeignOwned,LocationState.possible,Permission.isUnique] at owned <;> simp only [AccessOwned,Owned,LocalReadable,ForeignOwned] <;> decide

private theorem recorded_preserves (state recorded : LocationState) (actual owner : AccessRelatedness)
    (owned : AccessOwned state .Read owner false)
    (record : state.recordNewAccess .Read actual = .Recorded recorded) : AccessOwned recorded .Read owner false := by
  unfold LocationState.recordNewAccess at record
  split at record
  · cases record
    cases owner <;> exact owned
  · cases record

/-- Every actual normal event preserves ownership of an independently selected
Read anchor under empty protectors, including early-error states. -/
theorem events (items : List TraversalEvent) (root : Nat) (tree : NormalTreeState)
    (related : Nat → AccessRelatedness) (empty : tree.protectedNodes = [])
    (owned : Pointwise tree (fun _ => false) related) :
    Pointwise (sourceNormalEvents tree root .Read items).tree (fun _ => false) related := by
  induction items generalizing tree with
  | nil => unfold_normal_events;exact owned
  | cons event rest ih =>
    cases present : tree.stateAt event.node with
    | none => unfold_storage_events;simpa only [present] using owned
    | some state =>
      cases record : state.recordNewAccess .Read event.relatedness with
      | DebugAssertion => unfold_storage_events;simpa only [present,record] using owned
      | Recorded recorded =>
        have nextOwned : ∀ valid : event.node < tree.locationStates.size,
            Required (recorded.performAccess .Read event.relatedness (tree.protectedNodes.contains event.node)).resultingState
              false (related event.node) (tree.protectedNodes.contains event.node) := by
          intro valid
          obtain ⟨old,oldPresent,oldOwned⟩ := owned event.node valid
          have equal : old = state := Option.some.inj (oldPresent.symm.trans present)
          subst old
          have oldRead : AccessOwned state .Read (related event.node) false := by
            simpa [Required,empty] using oldOwned
          have recordedRead := recorded_preserves state recorded event.relatedness (related event.node) oldRead record
          simpa [Required,empty] using state_preserves recorded event.relatedness (related event.node) recordedRead
        cases access : recorded.performAccess .Read event.relatedness (tree.protectedNodes.contains event.node) <;>
          by_cases valid : event.node < tree.locationStates.size
        all_goals unfold_storage_events
        all_goals simp only [present,record,access,valid,↓reduceDIte,LocationState.AccessResult.resultingState]
        all_goals first
          | exact owned
          | exact ih _ empty (update_pointwise tree (fun _ => false) related owned event.node valid _ (by
              simpa only [access,LocationState.AccessResult.resultingState] using nextOwned valid))
          | exact update_pointwise tree (fun _ => false) related owned event.node valid _ (by
              simpa only [access,LocationState.AccessResult.resultingState] using nextOwned valid)

/-- Normal unprotected Read through any source retains the selected target's
Read ownership. The target need not lie on the source's ancestor path. -/
theorem normal (tree : NormalTreeState) (source target : Nat) (mode : ChildrenVisitMode)
    (empty : tree.protectedNodes = []) (owned : GeneralBorrowAnchor.AnchorOwned tree target .Read) :
    GeneralBorrowAnchor.AnchorOwned (tree.performAccess source .Read mode).tree target .Read := by
  have storage := GeneralBorrowStorage.events_storage (tree.topology.traverse source mode (sourceNormalSkipped tree .Read)).2
    (tree.topology.traverse source mode (sourceNormalSkipped tree .Read)).1 .Read tree
  change GeneralBorrowStorage.SameStorage tree (tree.performAccess source .Read mode).tree at storage
  have initial : Pointwise tree (fun _ => false) (GeneralBorrowAnchor.relation tree target) := by
    intro position valid
    exact owned.permissions position (by rw [←owned.locationsAligned];exact valid)
  have final := events (tree.topology.traverse source mode (sourceNormalSkipped tree .Read)).2
    (tree.topology.traverse source mode (sourceNormalSkipped tree .Read)).1 tree (GeneralBorrowAnchor.relation tree target) empty initial
  change Pointwise (tree.performAccess source .Read mode).tree (fun _ => false) (GeneralBorrowAnchor.relation tree target) at final
  refine ⟨?_,?_,?_,?_⟩
  · rw [storage.1];exact owned.anchorValid
  · rw [storage.2.2.2,storage.1];exact owned.locationsAligned
  · rw [storage.2.1,storage.1];exact owned.defaultsAligned
  · intro position valid
    have bound : position < (tree.performAccess source .Read mode).tree.locationStates.size := by
      rw [storage.2.2.2,owned.locationsAligned];rw [storage.1] at valid;exact valid
    obtain ⟨state,present,permitted⟩ := final position bound
    refine ⟨state,present,?_⟩
    simpa [Required,GeneralBorrowAnchor.relation,storage.1] using permitted

/-- Actual location Read/write-back keeps any previous Read anchor, without
requiring that anchor to be the operation's source. -/
theorem location (tree : BorrowTree) (location : LocationTree) (source target : UniIndex) (mode : ChildrenVisitMode)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (owned : GeneralBorrowRange.LocationOwned tree {} target .Read location) :
    GeneralBorrowRange.LocationOwned tree {} target .Read (tree.performNormalAccessAt location source .Read {} mode).location := by
  obtain ⟨⟨forest⟩,owner⟩ := owned
  have exactProjection := GeneralBorrowRangePreserves.normal_projection tree location {} source .Read mode fits
  have storage := GeneralBorrowStorage.events_storage
    ((source_normal_projection tree location {}).topology.traverse source.toNat mode (sourceNormalSkipped (source_normal_projection tree location {}) .Read)).2
    ((source_normal_projection tree location {}).topology.traverse source.toNat mode (sourceNormalSkipped (source_normal_projection tree location {}) .Read)).1
    .Read (source_normal_projection tree location {})
  change GeneralBorrowStorage.SameStorage (source_normal_projection tree location {})
    ((source_normal_projection tree location {}).performAccess source.toNat .Read mode).tree at storage
  have empty : (source_normal_projection tree location {}).protectedNodes = [] := by
    unfold_general_projection;simp [ProtectedTags.contains,ProtectedTags.get]
  refine ⟨?_,?_⟩
  · rw [exactProjection,storage.1];exact ⟨forest⟩
  · rw [exactProjection]
    exact normal _ source.toNat target.toNat mode empty owner

end DuplicatePrefix.GeneralBorrowUnprotectedReadOther
