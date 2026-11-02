import duplicate_prefix.GeneralBorrowFreshActiveOnClean
namespace DuplicatePrefix.GeneralBorrowEventTransitionMetadata
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowEvents DuplicatePrefix.GeneralBorrowPermissions DuplicatePrefix.GeneralBorrowStorage
open DuplicatePrefix.GeneralBorrowFreshActiveOnClean
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Recording traversal SIFA information does not alter the permission. -/
theorem record_permission (state recorded : LocationState) (kind : AccessKind) (related : AccessRelatedness)
    (record : state.recordNewAccess kind related = .Recorded recorded) : recorded.permission = state.permission := by
  unfold LocationState.recordNewAccess at record
  split at record
  · cases record;rfl
  · cases record

/-- A successful source per-node operation has the actual public permission
transition and endpoint. This is an extraction lemma, not a safety assumption. -/
theorem success_endpoint (state next : LocationState) (transition : PermTransition)
    (kind : AccessKind) (related : AccessRelatedness) (held : Bool)
    (access : state.performAccess kind related held = .Success next transition) :
    performAccessTransition kind related state.permission held = .Transition transition ∧
    transition.fromPermission = state.permission ∧ transition.toPermission = next.permission := by
  have fromSource : ∀ value, performAccessTransition kind related state.permission held = .Transition value →
      value.fromPermission = state.permission := by
    intro value found
    unfold performAccessTransition at found
    split at found
    · cases found;rfl
    · cases found
    · cases found
  unfold LocationState.performAccess at access
  cases performed : performAccessTransition kind related state.permission held with
  | UndefinedBehavior => simp only [performed] at access;cases access
  | ImpossibleProtectedReservedIM => simp only [performed] at access;cases access
  | Transition actual =>
    simp only [performed] at access
    cases applied : actual.applied state.permission with
    | none => simp only [applied] at access;cases access
    | some permission =>
      simp only [applied] at access
      split at access
      · cases access
      · split at access
        · cases access
        · cases access
          refine ⟨rfl,fromSource transition performed,?_⟩
          unfold PermTransition.applied at applied
          split at applied
          · exact Option.some.inj applied
          · cases applied

/-- Optional storage outside the event list is retained exactly; defaults and
protection metadata also remain unchanged, so effective stateAt is framed. -/
theorem unvisited (events : List TraversalEvent) (root : Nat) (kind : AccessKind)
    (tree : NormalTreeState) (position : Nat) (outside : ∀ event ∈ events, event.node ≠ position) :
    (sourceNormalEvents tree root kind events).tree.stateAt position = tree.stateAt position := by
  have slots := events_unvisited events root kind tree position outside
  have defaults := (events_storage events root kind tree).2.1
  simp only [NormalTreeState.stateAt,slots,defaults]

set_option autoImplicit false in
/-- Initial permission and exact final explicitly stored endpoint of one unique
scheduled source event. The source records SIFA first, but permission endpoints
come from performAccessTransition on the original effective permission. -/
structure Endpoint (tree : NormalTreeState) (events : List TraversalEvent) (root : Nat)
    (kind : AccessKind) (event : TraversalEvent) where
  oldState : LocationState
  newState : LocationState
  transition : PermTransition
  oldPresent : tree.stateAt event.node = some oldState
  finalStored : (sourceNormalEvents tree root kind events).tree.locationStates[event.node]? = some (some newState)
  performed : performAccessTransition kind event.relatedness oldState.permission (tree.protectedNodes.contains event.node) = .Transition transition
  fromPermission : transition.fromPermission = oldState.permission
  toPermission : transition.toPermission = newState.permission

/-- Every distinct scheduled owned event's final state is its own actual
permission-transition endpoint. Later visitors cannot overwrite that node.
The operation's completion is derived from EventsOwned, never assumed. -/
theorem events (items : List TraversalEvent) (root : Nat) (kind : AccessKind) (tree : NormalTreeState)
    (distinct : (items.map TraversalEvent.node).Nodup) (owned : EventsOwned tree kind items) :
    ∀ event ∈ items, Nonempty (Endpoint tree items root kind event) := by
  induction items generalizing tree with
  | nil => intro event member;cases member
  | cons head rest ih =>
    obtain ⟨old,present,valid,compatible,scheduled⟩ := owned head (by simp)
    obtain ⟨recorded,next,transition,record,access,preserved⟩ :=
      (visit_for_success old kind head.relatedness (tree.protectedNodes.contains head.node) compatible).resolve_left
        (by rw [scheduled_recurse old kind head.relatedness scheduled];decide)
    have endpoints := success_endpoint recorded next transition kind head.relatedness (tree.protectedNodes.contains head.node) access
    have permission := record_permission old recorded kind head.relatedness record
    let updated := {tree with locationStates := tree.locationStates.set head.node (some next) valid}
    have step : sourceNormalEvents tree root kind (head :: rest) =
        {sourceNormalEvents updated root kind rest with visited := head :: (sourceNormalEvents updated root kind rest).visited} := by
      unfold_normal_events
      simp only [present,record,access,valid,↓reduceDIte]
      rfl
    have nodup := List.nodup_cons.mp distinct
    have laterOwned : EventsOwned updated kind rest := by
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
      have untouched := events_unvisited rest root kind updated head.node outside
      have stored : (sourceNormalEvents updated root kind rest).tree.locationStates[head.node]? = some (some next) := by
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

end DuplicatePrefix.GeneralBorrowEventTransitionMetadata
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowEventTransitionMetadata.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved generic event-transition metadata dependency {dependency}"
