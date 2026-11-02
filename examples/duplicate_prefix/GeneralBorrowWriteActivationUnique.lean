import duplicate_prefix.GeneralBorrowReadUnique

namespace DuplicatePrefix.GeneralBorrowWriteActivationUnique
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowEvents DuplicatePrefix.GeneralBorrowPermissions DuplicatePrefix.GeneralBorrowFreshActiveOnClean
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private theorem local_unique (state : LocationState) (held : Bool)
    (owned : LocalOwned state held) (notCell : state.permission ≠ .Cell) :
    (state.performAccess .Write .LocalAccess held).resultingState.permission = .Unique := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases accessed <;> cases sifa <;> cases held <;>
      (simp [LocalOwned,LocationState.possible,Permission.isUnique] at owned) <;> rfl
  | Cell => exact False.elim (notCell rfl)
  | ReservedIM | Unique | Frozen | Disabled =>
    cases accessed <;> cases sifa <;> cases held <;>
      (simp [LocalOwned,LocationState.possible,Permission.isUnique] at owned) <;> rfl

private theorem record_permission (state recorded : LocationState)
    (record : state.recordNewAccess .Write .LocalAccess = .Recorded recorded) :
    recorded.permission = state.permission := by
  unfold LocationState.recordNewAccess at record
  split at record
  · cases record;rfl
  · cases record

/-- The real selected local Write makes every non-Cell writable permission
Unique. This includes Default reservations; it assumes no operation success. -/
theorem event_activates (tree : NormalTreeState) (root position : Nat) (state : LocationState)
    (present : tree.stateAt position = some state) (valid : position < tree.locationStates.size)
    (owned : LocalOwned state (tree.protectedNodes.contains position)) (notCell : state.permission ≠ .Cell) :
    ∃ next, next.permission = .Unique ∧ ∀ rest,
      sourceNormalEvents tree root .Write (⟨position,.LocalAccess⟩ :: rest) =
        let later := sourceNormalEvents {tree with locationStates := tree.locationStates.set position (some next) valid} root .Write rest
        {later with visited := ⟨position,.LocalAccess⟩ :: later.visited} := by
  obtain ⟨recorded,next,transition,record,access,preserved⟩ :=
    (visit_for_success state .Write .LocalAccess (tree.protectedNodes.contains position) owned).resolve_left
      (by rw [scheduled_recurse state .Write .LocalAccess (Or.inl rfl)];decide)
  have recordOwned : LocalOwned recorded (tree.protectedNodes.contains position) := by
    unfold LocationState.recordNewAccess at record
    split at record
    · cases record;exact owned
    · cases record
  have unique : next.permission = .Unique := by
    have result := local_unique recorded (tree.protectedNodes.contains position) recordOwned
      (fun same => notCell ((record_permission state recorded record).symm.trans same))
    simpa only [access,LocationState.AccessResult.resultingState] using result
  refine ⟨next,unique,?_⟩
  intro rest
  unfold_normal_events
  simp only [present,record,access,valid,↓reduceDIte]
  rfl

/-- A distinct owned event schedule containing the selected local Write stores
Unique at that slot. All success facts are derived from the event data. -/
theorem events_activate (events : List TraversalEvent) (root position : Nat) (tree : NormalTreeState)
    (distinct : (events.map TraversalEvent.node).Nodup) (owned : EventsOwned tree .Write events)
    (member : (⟨position,.LocalAccess⟩ : TraversalEvent) ∈ events)
    (localEvents : ∀ event ∈ events, event.node = position → event.relatedness = .LocalAccess)
    (notCell : ∀ state, tree.stateAt position = some state → state.permission ≠ .Cell) :
    GeneralBorrowReadUnique.StoredUnique (sourceNormalEvents tree root .Write events).tree position := by
  induction events generalizing tree with
  | nil => cases member
  | cons event rest ih =>
    have distinctParts := List.nodup_cons.mp distinct
    obtain ⟨state,present,valid,compatible,scheduled⟩ := owned event (by simp)
    by_cases same : event.node = position
    · have related := localEvents event (by simp) same
      have eventEq : event = ⟨position,.LocalAccess⟩ := by cases event;cases same;cases related;rfl
      subst event
      obtain ⟨next,unique,step⟩ := event_activates tree root position state present valid compatible (notCell state present)
      rw [step]
      have outside : ∀ later ∈ rest, later.node ≠ position := by
        intro later inRest equal
        exact distinctParts.1 (List.mem_map.mpr ⟨later,inRest,equal⟩)
      refine ⟨next,?_,unique⟩
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
      · intro later inRest;exact localEvents later (by simp [inRest])
      · intro old oldPresent
        apply notCell old
        rw [stateAt_update_other tree event.node position next valid (Ne.symm same)] at oldPresent
        exact oldPresent

/-- The actual normal selected Write stores Unique when its initial effective
permission is non-Cell and writable. Success is derived from the forest/owner
contract; no successful normal access is an input. -/
theorem normal (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (mode : ChildrenVisitMode)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location protections) anchor.toNat .Write)
    (notCell : ∀ state, (source_normal_projection tree location protections).stateAt anchor.toNat = some state → state.permission ≠ .Cell) :
    ∃ state, (tree.performNormalAccessAt location anchor .Write protections mode).location.perms.get anchor = some state ∧
      state.permission = .Unique := by
  let normal := source_normal_projection tree location protections
  let events := (normal.topology.traverse anchor.toNat mode (sourceNormalSkipped normal .Write)).2
  have schedule := GeneralBorrowTraversal.traversal_data normal.topology forest anchor.toNat owned.anchorValid mode (sourceNormalSkipped normal .Write)
  have selfPath : anchor.toNat ∈ normal.topology.ancestorPath anchor.toNat := by
    change anchor.toNat ∈ sourceAncestorPath normal.topology normal.topology.nodes.size anchor.toNat
    cases normal.topology.nodes.size with
    | zero => simp only [GeneralBorrowPresence.ancestor_zero,List.mem_singleton]
    | succ fuel => rw [GeneralBorrowPresence.ancestor_succ];split <;> simp
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
          anchor.toNat mode event member related
        have cannotSkip : state.skipIfKnownNoop .Write .ForeignAccess ≠ .SkipSelfAndChildren := by
          intro skip
          exact unskipped ((skipped_iff normal .Write event.node state present shape.1).mpr skip)
        cases skip : state.skipIfKnownNoop .Write .ForeignAccess with
        | Recurse => rfl
        | SkipSelfAndChildren => exact False.elim (cannotSkip skip)
  have member : (⟨anchor.toNat,.LocalAccess⟩ : TraversalEvent) ∈ events := by
    have head : events.head? = some ⟨anchor.toNat,.LocalAccess⟩ :=
      TraversalTree.traverse_starts_at_accessed_node normal.topology anchor.toNat mode (sourceNormalSkipped normal .Write)
    cases found : events with
    | nil => simp only [found,List.head?_nil] at head;cases head
    | cons event rest =>
      have same : event = ⟨anchor.toNat,.LocalAccess⟩ := Option.some.inj (by simpa only [found,List.head?_cons] using head)
      simp only [same,List.mem_cons,true_or]
  have final := events_activate events (normal.topology.traverse anchor.toNat mode (sourceNormalSkipped normal .Write)).1 anchor.toNat normal
    schedule.1 pointwise member (by
      intro event inEvents equal
      simpa only [equal,selfPath,ite_true] using (schedule.2 event inEvents).2) notCell
  change GeneralBorrowReadUnique.StoredUnique (normal.performAccess anchor.toNat .Write mode).tree anchor.toNat at final
  obtain ⟨state,stored,permission⟩ := final
  refine ⟨state,?_,permission⟩
  rw [source_normal_perms]
  unfold_clean_write_states
  simp only [Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  change (forIn _ location (source_write_scan _)).perms.get anchor = some state
  rw [source_write_list_get]
  have bounded : anchor.toNat < (normal.performAccess anchor.toNat .Write mode).tree.locationStates.size :=
    (Array.getElem?_eq_some_iff.mp stored).1
  have row := (Array.getElem?_eq_some_iff.mp stored).2
  dsimp only [normal] at bounded row stored
  simp [List.mem_range',bounded,stored,row,Option.or]

end DuplicatePrefix.GeneralBorrowWriteActivationUnique
