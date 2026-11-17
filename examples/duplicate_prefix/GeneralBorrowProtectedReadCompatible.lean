import duplicate_prefix.GeneralBorrowTraversal
import duplicate_prefix.GeneralBorrowEventTransitionMetadata
import duplicate_prefix.GeneralBorrowProtectedChildReadSchedule
namespace DuplicatePrefix.GeneralBorrowProtectedReadCompatible
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowEvents
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Initial permission compatibility for an actual Read. Active protected
reservations are explicitly allowed at foreign nodes. Held Unique and
ReservedIM remain excluded, preserving the pinned source error checks. -/
def Compatible (state : LocationState) (related : AccessRelatedness) (held : Bool) : Prop :=
  state.possible = true ∧ match related with
  | .LocalAccess => state.permission ≠ .Disabled
  | .ForeignAccess => held = true → state.permission ≠ .Unique ∧ state.permission ≠ .ReservedIM ∧ (state.permission = .Disabled → state.accessed = false)

theorem reservation (conflicted accessed : Bool) (sifa : IdempotentForeignAccess) (held : Bool) :
    Compatible ⟨.ReservedFrz conflicted,accessed,sifa⟩ .ForeignAccess held := by
  cases conflicted <;> cases accessed <;> cases held <;> simp [Compatible,LocationState.possible,Permission.isUnique]

private theorem access (state : LocationState) (related : AccessRelatedness) (held : Bool)
    (initial : Compatible state related held) :
    ∃ next transition,state.performAccess .Read related held = .Success next transition := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases accessed <;> cases sifa <;> cases related <;> cases held <;>
      simp [Compatible,LocationState.possible,Permission.isUnique] at initial <;> exact ⟨_,_,rfl⟩
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases accessed <;> cases sifa <;> cases related <;> cases held <;>
      simp [Compatible,LocationState.possible,Permission.isUnique] at initial <;> exact ⟨_,_,rfl⟩

private theorem event_cons (tree : NormalTreeState) (root : Nat) (event : TraversalEvent) (state : LocationState)
    (present : tree.stateAt event.node = some state) (valid : event.node < tree.locationStates.size)
    (initial : Compatible state event.relatedness (tree.protectedNodes.contains event.node))
    (scheduled : Scheduled state .Read event.relatedness) :
    ∃ next,∀ rest,sourceNormalEvents tree root .Read (event::rest) =
      let later := sourceNormalEvents {tree with locationStates := tree.locationStates.set event.node (some next) valid} root .Read rest
      {later with visited := event::later.visited} := by
  let recorded := {state with idempotentForeignAccess := (IdempotentForeignAccess.recordNew state.idempotentForeignAccess
    (IdempotentForeignAccess.fromAccessAndRelatedness .Read event.relatedness))}
  have compatible : Compatible recorded event.relatedness (tree.protectedNodes.contains event.node) := initial
  obtain ⟨next,transition,performed⟩ := access recorded event.relatedness (tree.protectedNodes.contains event.node) compatible
  have record : state.recordNewAccess .Read event.relatedness = .Recorded recorded := by
    simp only [LocationState.recordNewAccess,scheduled_recurse state .Read event.relatedness scheduled,beq_self_eq_true,↓reduceIte]
    rfl
  refine ⟨next,?_⟩
  intro rest
  unfold_normal_events
  simp only [present,record,performed,valid,↓reduceDIte]
  rfl

private theorem events (items : List TraversalEvent) (root : Nat) (tree : NormalTreeState)
    (distinct : (items.map TraversalEvent.node).Nodup)
    (initial : ∀ event ∈ items,∃ state,tree.stateAt event.node = some state ∧ event.node < tree.locationStates.size ∧
      Compatible state event.relatedness (tree.protectedNodes.contains event.node) ∧ Scheduled state .Read event.relatedness) :
    (sourceNormalEvents tree root .Read items).status = .Completed := by
  induction items generalizing tree with
  | nil => unfold_normal_events
  | cons event rest ih =>
    obtain ⟨state,present,valid,compatible,scheduled⟩ := initial event (by simp)
    obtain ⟨next,step⟩ := event_cons tree root event state present valid compatible scheduled
    rw [step]
    simp only [List.map_cons,List.nodup_cons] at distinct
    apply ih _ distinct.2
    intro later member
    obtain ⟨old,oldPresent,oldValid,oldCompatible,oldScheduled⟩ := initial later (by simp [member])
    have different : later.node ≠ event.node := by
      intro same
      exact distinct.1 (List.mem_map.mpr ⟨later,member,same⟩)
    refine ⟨old,?_,?_,oldCompatible,oldScheduled⟩
    · rw [stateAt_update_other tree event.node later.node next valid different];exact oldPresent
    · simpa using oldValid

/-- Completion of the actual source Read visitor for arbitrary ranked forests,
including simultaneously held active foreign Default reservations. The real
visitor derives distinctness, relatedness and SIFA scheduling. -/
theorem normal (tree : NormalTreeState) (forest : GeneralBorrowForest.Forest tree.topology)
    (anchor : Nat) (valid : anchor < tree.topology.nodes.size) (mode : ChildrenVisitMode)
    (aligned : tree.locationStates.size = tree.topology.nodes.size)
    (initial : ∀ index,index < tree.topology.nodes.size → ∃ state,tree.stateAt index = some state ∧
      Compatible state (GeneralBorrowAnchor.relation tree anchor index) (tree.protectedNodes.contains index)) :
    (tree.performAccess anchor .Read mode).status = .Completed := by
  have schedule := GeneralBorrowTraversal.traversal_data tree.topology forest anchor valid mode (sourceNormalSkipped tree .Read)
  unfold NormalTreeState.performAccess
  apply events _ _ tree schedule.1
  intro event member
  have shape := schedule.2 event member
  obtain ⟨state,present,compatible⟩ := initial event.node shape.1
  refine ⟨state,present,by omega,?_,?_⟩
  · simpa only [GeneralBorrowAnchor.relation,←shape.2] using compatible
  · apply recurse_scheduled
    cases related : event.relatedness with
    | LocalAccess => rfl
    | ForeignAccess =>
      have notSkipped := GeneralBorrowTopology.traversal_foreign_not_skipped tree.topology
        (sourceNormalSkipped tree .Read) anchor mode event member related
      have noSkip : state.skipIfKnownNoop .Read .ForeignAccess ≠ .SkipSelfAndChildren := by
        intro skipped
        exact notSkipped ((skipped_iff tree .Read event.node state present shape.1).mpr skipped)
      cases skip : state.skipIfKnownNoop .Read .ForeignAccess with
      | Recurse => rfl
      | SkipSelfAndChildren => exact False.elim (noSkip skip)
theorem endpoints (items : List TraversalEvent) (root : Nat) (tree : NormalTreeState)
    (distinct : (items.map TraversalEvent.node).Nodup) (owned : (∀ event ∈ items,∃ state,tree.stateAt event.node = some state ∧ event.node < tree.locationStates.size ∧ Compatible state event.relatedness (tree.protectedNodes.contains event.node) ∧ Scheduled state .Read event.relatedness)) :
    ∀ event ∈ items, Nonempty (GeneralBorrowEventTransitionMetadata.Endpoint tree items root .Read event) := by
  induction items generalizing tree with
  | nil => intro event member;cases member
  | cons head rest ih =>
    obtain ⟨old,present,valid,compatible,scheduled⟩ := owned head (by simp)
    let recorded := {old with idempotentForeignAccess := (IdempotentForeignAccess.recordNew old.idempotentForeignAccess
      (IdempotentForeignAccess.fromAccessAndRelatedness .Read head.relatedness))}
    have record : old.recordNewAccess .Read head.relatedness = .Recorded recorded := by
      simp only [LocationState.recordNewAccess,scheduled_recurse old .Read head.relatedness scheduled,beq_self_eq_true,↓reduceIte]
      rfl
    have compatibleRecorded : Compatible recorded head.relatedness (tree.protectedNodes.contains head.node) := compatible
    obtain ⟨next,transition,access⟩ := access recorded head.relatedness (tree.protectedNodes.contains head.node) compatibleRecorded
    have endpoints := GeneralBorrowEventTransitionMetadata.success_endpoint recorded next transition .Read head.relatedness (tree.protectedNodes.contains head.node) access
    have permission := GeneralBorrowEventTransitionMetadata.record_permission old recorded .Read head.relatedness record
    let updated := {tree with locationStates := tree.locationStates.set head.node (some next) valid}
    have step : sourceNormalEvents tree root .Read (head :: rest) =
        {sourceNormalEvents updated root .Read rest with visited := head :: (sourceNormalEvents updated root .Read rest).visited} := by
      unfold_normal_events
      simp only [present,record,access,valid,↓reduceDIte]
      rfl
    have nodup := List.nodup_cons.mp distinct
    have laterOwned : (∀ event ∈ rest,∃ state,updated.stateAt event.node = some state ∧ event.node < updated.locationStates.size ∧ Compatible state event.relatedness (updated.protectedNodes.contains event.node) ∧ Scheduled state .Read event.relatedness) := by
      intro later member
      obtain ⟨state,found,bounded,compatible,scheduled⟩ := owned later (by simp [member])
      have different : later.node ≠ head.node := by
        intro same;exact nodup.1 (List.mem_map.mpr ⟨later,member,same⟩)
      exact ⟨state,(stateAt_update_other tree head.node later.node next valid different).trans found,
        by simpa only [updated,Array.size_set] using bounded,compatible,scheduled⟩
    intro event member
    rcases List.mem_cons.mp member with same | later
    · subst event
      have outside : ∀ event ∈ rest, event.node ≠ head.node := by
        intro event member same;exact nodup.1 (List.mem_map.mpr ⟨event,member,same⟩)
      have untouched := GeneralBorrowFreshActiveOnClean.events_unvisited rest root .Read updated head.node outside
      have stored : (sourceNormalEvents updated root .Read rest).tree.locationStates[head.node]? = some (some next) := by
        rw [untouched]
        simp only [updated,Array.getElem?_set_self]
      refine ⟨⟨old,next,transition,present,?_,?_,?_,endpoints.2.2⟩⟩
      · rw [step];exact stored
      · rw [←permission];exact endpoints.1
      · exact endpoints.2.1.trans permission
    · obtain ⟨facts⟩ := ih updated nodup.2 laterOwned event later
      have different : event.node ≠ head.node := by
        intro same;exact nodup.1 (List.mem_map.mpr ⟨event,later,same⟩)
      refine ⟨⟨facts.oldState,facts.newState,facts.transition,?_,?_,facts.performed,facts.fromPermission,facts.toPermission⟩⟩
      · have oldPresent := facts.oldPresent
        rw [stateAt_update_other tree head.node event.node next valid different] at oldPresent
        exact oldPresent
      · rw [step];exact facts.finalStored

/-- Exact source transition endpoints under the broader protected Read compatibility. -/
theorem normal_endpoints (tree : NormalTreeState) (forest : GeneralBorrowForest.Forest tree.topology)
    (anchor : Nat) (valid : anchor < tree.topology.nodes.size) (mode : ChildrenVisitMode)
    (aligned : tree.locationStates.size = tree.topology.nodes.size)
    (initial : ∀ index,index < tree.topology.nodes.size → ∃ state,tree.stateAt index = some state ∧
      Compatible state (GeneralBorrowAnchor.relation tree anchor index) (tree.protectedNodes.contains index)) :
    ∀ event ∈ (tree.topology.traverse anchor mode (sourceNormalSkipped tree .Read)).2,
      Nonempty (GeneralBorrowEventTransitionMetadata.Endpoint tree
        (tree.topology.traverse anchor mode (sourceNormalSkipped tree .Read)).2
        (tree.topology.traverse anchor mode (sourceNormalSkipped tree .Read)).1 .Read event) := by
  have schedule := GeneralBorrowTraversal.traversal_data tree.topology forest anchor valid mode (sourceNormalSkipped tree .Read)
  apply endpoints _ _ tree schedule.1
  intro event member
  have shape := schedule.2 event member
  obtain ⟨state,present,compatible⟩ := initial event.node shape.1
  refine ⟨state,present,by omega,?_,?_⟩
  · simpa only [GeneralBorrowAnchor.relation,←shape.2] using compatible
  · apply recurse_scheduled
    cases related : event.relatedness with
    | LocalAccess => rfl
    | ForeignAccess =>
      have notSkipped := GeneralBorrowTopology.traversal_foreign_not_skipped tree.topology
        (sourceNormalSkipped tree .Read) anchor mode event member related
      have noSkip : state.skipIfKnownNoop .Read .ForeignAccess ≠ .SkipSelfAndChildren := by
        intro skipped
        exact notSkipped ((skipped_iff tree .Read event.node state present shape.1).mpr skipped)
      cases skip : state.skipIfKnownNoop .Read .ForeignAccess with
      | Recurse => rfl
      | SkipSelfAndChildren => exact False.elim (noSkip skip)
/-- The actual constructor-leading root Read reaches an earlier held active
reservation and stores its conflict, without the old strong ForeignOwned
premise. Arbitrary sibling and descendant subtrees remain permitted. -/
theorem root_conflict (tree : NormalTreeState) (forest : GeneralBorrowForest.Forest tree.topology)
    (root earlier : Nat) (valid : root < tree.topology.nodes.size)
    (parentless : tree.topology.nodes[root].parent = none)
    (listed : earlier ∈ tree.topology.nodes[root].children)
    (aligned : tree.locationStates.size = tree.topology.nodes.size)
    (initial : ∀ index,index < tree.topology.nodes.size → ∃ state,tree.stateAt index = some state ∧
      Compatible state (GeneralBorrowAnchor.relation tree root index) (tree.protectedNodes.contains index))
    (state : LocationState) (present : tree.stateAt earlier = some state)
    (held : tree.protectedNodes.contains earlier = true) (reservation : state.permission = .ReservedFrz false)
    (consistent : GeneralBorrowSifaPermissionConsistency.Consistent state true) :
    (tree.performAccess root .Read .VisitChildrenOfAccessed).status = .Completed ∧
    ∃ next,(tree.performAccess root .Read .VisitChildrenOfAccessed).tree.locationStates[earlier]? = some (some next) ∧
      next.permission = .ReservedFrz true := by
  have scheduled := GeneralBorrowProtectedChildReadSchedule.direct_child tree forest root earlier valid
    parentless listed state present held reservation consistent
  have complete := normal tree forest root valid .VisitChildrenOfAccessed aligned initial
  obtain ⟨endpoint⟩ := normal_endpoints tree forest root valid .VisitChildrenOfAccessed aligned initial
    ⟨earlier,.ForeignAccess⟩ scheduled
  have old : endpoint.oldState = state := Option.some.inj (endpoint.oldPresent.symm.trans present)
  have transition := endpoint.performed
  simp only [old,reservation,held] at transition
  have expected : performAccessTransition .Read .ForeignAccess (.ReservedFrz false) true =
      .Transition ⟨.ReservedFrz false,.ReservedFrz true⟩ := rfl
  have same := PermTransitionOutcome.Transition.inj (transition.symm.trans expected)
  have endpointPermission := endpoint.toPermission
  rw [same] at endpointPermission
  exact ⟨complete,endpoint.newState,endpoint.finalStored,endpointPermission.symm⟩

end DuplicatePrefix.GeneralBorrowProtectedReadCompatible
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedReadCompatible.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protected Read compatibility dependency {dependency}"
