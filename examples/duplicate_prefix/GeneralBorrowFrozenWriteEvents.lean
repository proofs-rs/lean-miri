import duplicate_prefix.GeneralBorrowWriteActivationUnique
namespace DuplicatePrefix.GeneralBorrowFrozenWriteEvents
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowEvents DuplicatePrefix.GeneralBorrowPermissions DuplicatePrefix.GeneralBorrowFreshActiveOnClean
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def StoredDisabled (tree : NormalTreeState) (position : Nat) : Prop :=
  ∃ state, tree.locationStates[position]? = some (some state) ∧ state.permission = .Disabled

private theorem foreign_disabled (state : LocationState) (frozen : state.permission = .Frozen) :
    (state.performAccess .Write .ForeignAccess false).resultingState.permission = .Disabled := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases frozen
  cases accessed <;> cases sifa <;> rfl

private theorem record_permission (state recorded : LocationState)
    (record : state.recordNewAccess .Write .ForeignAccess = .Recorded recorded) :
    recorded.permission = state.permission := by
  unfold LocationState.recordNewAccess at record
  split at record
  · cases record;rfl
  · cases record

/-- A real scheduled unprotected foreign Write changes Frozen to Disabled;
recording and transition success are derived from data. -/
theorem event_disables (tree : NormalTreeState) (root position : Nat) (state : LocationState)
    (present : tree.stateAt position = some state) (valid : position < tree.locationStates.size)
    (owned : ForeignOwned state (tree.protectedNodes.contains position)) (scheduled : Scheduled state .Write .ForeignAccess)
    (unheld : tree.protectedNodes.contains position = false) (frozen : state.permission = .Frozen) :
    ∃ next, next.permission = .Disabled ∧ ∀ rest,
      sourceNormalEvents tree root .Write (⟨position,.ForeignAccess⟩ :: rest) =
        let later := sourceNormalEvents {tree with locationStates := tree.locationStates.set position (some next) valid} root .Write rest
        {later with visited := ⟨position,.ForeignAccess⟩ :: later.visited} := by
  obtain ⟨recorded,next,transition,record,access,preserved⟩ :=
    (visit_for_success state .Write .ForeignAccess (tree.protectedNodes.contains position) owned).resolve_left
      (by rw [scheduled_recurse state .Write .ForeignAccess scheduled];decide)
  have recordOwned : ForeignOwned recorded (tree.protectedNodes.contains position) := by
    unfold LocationState.recordNewAccess at record
    split at record
    · cases record;exact owned
    · cases record
  have disabled : next.permission = .Disabled := by
    have exactPerm : recorded.permission = .Frozen := (record_permission state recorded record).trans frozen
    have result := foreign_disabled recorded exactPerm
    rw [unheld] at access
    simpa only [access,LocationState.AccessResult.resultingState] using result
  refine ⟨next,disabled,?_⟩
  intro rest
  unfold_normal_events
  simp only [present,record,access,valid,↓reduceDIte]
  rfl

/-- A distinct owned event schedule containing a selected Frozen foreign Write
stores Disabled at that slot. All success facts are derived from event data. -/
theorem events_disable (events : List TraversalEvent) (root position : Nat) (tree : NormalTreeState)
    (distinct : (events.map TraversalEvent.node).Nodup) (owned : EventsOwned tree .Write events)
    (member : (⟨position,.ForeignAccess⟩ : TraversalEvent) ∈ events)
    (foreignEvents : ∀ event ∈ events, event.node = position → event.relatedness = .ForeignAccess)
    (unheld : tree.protectedNodes.contains position = false)
    (frozen : ∀ state, tree.stateAt position = some state → state.permission = .Frozen) :
    StoredDisabled (sourceNormalEvents tree root .Write events).tree position := by
  induction events generalizing tree with
  | nil => cases member
  | cons event rest ih =>
    have distinctParts := List.nodup_cons.mp distinct
    obtain ⟨state,present,valid,compatible,scheduled⟩ := owned event (by simp)
    by_cases same : event.node = position
    · have related := foreignEvents event (by simp) same
      have eventEq : event = ⟨position,.ForeignAccess⟩ := by cases event;cases same;cases related;rfl
      subst event
      obtain ⟨next,disabled,step⟩ := event_disables tree root position state present valid compatible scheduled unheld (frozen state present)
      rw [step]
      have outside : ∀ later ∈ rest, later.node ≠ position := by
        intro later inRest equal
        exact distinctParts.1 (List.mem_map.mpr ⟨later,inRest,equal⟩)
      refine ⟨next,?_,disabled⟩
      rw [events_unvisited rest root .Write _ position outside]
      simp
    · obtain ⟨next,preserved,step⟩ := event_cons tree root event .Write state present valid compatible scheduled
      rw [step]
      apply ih _ distinctParts.2
      · intro later inRest
        obtain ⟨old,oldPresent,oldValid,oldOwned,oldScheduled⟩ := owned later (by simp [inRest])
        have different : later.node ≠ event.node := by
          intro equal
          exact distinctParts.1 (List.mem_map.mpr ⟨later,inRest,equal⟩)
        exact ⟨old,by rw [stateAt_update_other tree event.node later.node next valid different];exact oldPresent,
          by simpa using oldValid,oldOwned,oldScheduled⟩
      · rcases List.mem_cons.mp member with eq | inRest
        · exact False.elim (same (congrArg TraversalEvent.node eq.symm))
        · exact inRest
      · intro later inRest;exact foreignEvents later (by simp [inRest])
      · exact unheld
      · intro old oldPresent
        apply frozen old
        rw [stateAt_update_other tree event.node position next valid (Ne.symm same)] at oldPresent
        exact oldPresent

end DuplicatePrefix.GeneralBorrowFrozenWriteEvents
