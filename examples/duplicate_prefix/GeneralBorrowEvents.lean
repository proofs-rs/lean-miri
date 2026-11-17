import Lean
import duplicate_prefix.GeneralBorrowPermissions
namespace DuplicatePrefix.GeneralBorrowEvents
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowPermissions
open Lean Elab Tactic
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
private def sourceHelper (suffix : String) : CoreM Name := do
  let candidates := (← getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith suffix then some name else none
  match candidates with
  | [name] => pure name
  | _ => throwError "expected one actual source helper {suffix}"
elab "sourceNormalEvents" : term => return mkConst (← sourceHelper ".NormalTreeState.processEvents")
elab "sourceNormalSkipped" : term => return mkConst (← sourceHelper ".NormalTreeState.skippedForeignNodes")
elab "unfold_normal_skips" : tactic => do
  let name := mkIdent (← sourceHelper ".NormalTreeState.skippedForeignNodes")
  evalTactic (← `(tactic| unfold $name:ident))
elab "unfold_normal_events" : tactic => do
  let process := mkIdent (← sourceHelper ".NormalTreeState.processEvents")
  let update := mkIdent (← sourceHelper ".NormalTreeState.setState")
  evalTactic (← `(tactic| simp only [$process:ident, $update:ident]))

/-- Cache and permission data ensuring that a scheduled node is not pruned.
Skipped foreign nodes need no transition or ownership hypothesis. -/
def Scheduled (state : LocationState) (kind : AccessKind) (related : AccessRelatedness) : Prop :=
  related = .LocalAccess ∨
    (state.idempotentForeignAccess.rank < (IdempotentForeignAccess.fromForeign kind).rank ∧
      state.permission ≠ .Disabled ∧ (kind = .Read → state.permission ≠ .Frozen))

theorem scheduled_recurse (state : LocationState) (kind : AccessKind)
    (related : AccessRelatedness) (scheduled : Scheduled state kind related) :
    state.skipIfKnownNoop kind related = .Recurse := by
  rcases state with ⟨permission, accessed, sifa⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases sifa <;> cases kind <;> cases related <;>
      simp_all [Scheduled, LocationState.skipIfKnownNoop, AccessRelatedness.isForeign,
        IdempotentForeignAccess.fromForeign,IdempotentForeignAccess.rank,
        IdempotentForeignAccess.canSkipForeignAccess,IdempotentForeignAccess.isLocal,
        IdempotentForeignAccess.le,Permission.isDisabled,Permission.isFrozen]
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases sifa <;> cases kind <;> cases related <;>
      simp_all [Scheduled, LocationState.skipIfKnownNoop, AccessRelatedness.isForeign,
        IdempotentForeignAccess.fromForeign,IdempotentForeignAccess.rank,
        IdempotentForeignAccess.canSkipForeignAccess,IdempotentForeignAccess.isLocal,
        IdempotentForeignAccess.le,Permission.isDisabled,Permission.isFrozen]

theorem recurse_scheduled (state : LocationState) (kind : AccessKind)
    (related : AccessRelatedness) (recurse : state.skipIfKnownNoop kind related = .Recurse) :
    Scheduled state kind related := by
  rcases state with ⟨permission, accessed, sifa⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases sifa <;> cases kind <;> cases related <;>
      simp_all [Scheduled, LocationState.skipIfKnownNoop, AccessRelatedness.isForeign,
        IdempotentForeignAccess.fromForeign,IdempotentForeignAccess.rank,
        IdempotentForeignAccess.canSkipForeignAccess,IdempotentForeignAccess.isLocal,
        IdempotentForeignAccess.le,Permission.isDisabled,Permission.isFrozen]
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases sifa <;> cases kind <;> cases related <;>
      simp_all [Scheduled, LocationState.skipIfKnownNoop, AccessRelatedness.isForeign,
        IdempotentForeignAccess.fromForeign,IdempotentForeignAccess.rank,
        IdempotentForeignAccess.canSkipForeignAccess,IdempotentForeignAccess.isLocal,
        IdempotentForeignAccess.le,Permission.isDisabled,Permission.isFrozen]

theorem singleton_event (tree : NormalTreeState) (root : Nat) (event : TraversalEvent)
    (kind : AccessKind) (state : LocationState)
    (present : tree.stateAt event.node = some state)
    (valid : event.node < tree.locationStates.size)
    (owned : AccessOwned state kind event.relatedness (tree.protectedNodes.contains event.node))
    (scheduled : Scheduled state kind event.relatedness) :
    ∃ next,
      (sourceNormalEvents tree root kind [event]).status = .Completed ∧
      (sourceNormalEvents tree root kind [event]).tree.locationStates =
        tree.locationStates.set event.node (some next) valid ∧
      AccessOwned next kind event.relatedness (tree.protectedNodes.contains event.node) := by
  obtain ⟨recorded,next,transition,record,access,preserved⟩ :=
    (visit_for_success state kind event.relatedness (tree.protectedNodes.contains event.node) owned).resolve_left
      (by rw [scheduled_recurse state kind event.relatedness scheduled]; decide)
  refine ⟨next,?_,?_,preserved⟩
  all_goals unfold_normal_events
  all_goals simp only [present,record,access,valid,↓reduceDIte]
  all_goals rfl
theorem stateAt_update_other (tree : NormalTreeState) (index other : Nat)
    (next : LocationState) (valid : index < tree.locationStates.size) (different : other ≠ index) :
    ({tree with locationStates := tree.locationStates.set index (some next) valid} : NormalTreeState).stateAt other =
      tree.stateAt other := by
  simp [NormalTreeState.stateAt, Ne.symm different]

theorem event_cons (tree : NormalTreeState) (root : Nat) (event : TraversalEvent)
    (kind : AccessKind) (state : LocationState)
    (present : tree.stateAt event.node = some state)
    (valid : event.node < tree.locationStates.size)
    (owned : AccessOwned state kind event.relatedness (tree.protectedNodes.contains event.node))
    (scheduled : Scheduled state kind event.relatedness) :
    ∃ next, AccessOwned next kind event.relatedness (tree.protectedNodes.contains event.node) ∧
      ∀ rest, sourceNormalEvents tree root kind (event :: rest) =
        let later := sourceNormalEvents
          {tree with locationStates := tree.locationStates.set event.node (some next) valid} root kind rest
        {later with visited := event :: later.visited} := by
  obtain ⟨recorded,next,transition,record,access,preserved⟩ :=
    (visit_for_success state kind event.relatedness (tree.protectedNodes.contains event.node) owned).resolve_left
      (by rw [scheduled_recurse state kind event.relatedness scheduled]; decide)
  refine ⟨next,preserved,?_⟩
  intro rest
  unfold_normal_events
  simp only [present,record,access,valid,↓reduceDIte]
  rfl

/-- Initial states and array bounds for every scheduled event. This is a
pointwise data invariant, not an operation-success assumption. -/
def EventsOwned (tree : NormalTreeState) (kind : AccessKind) (events : List TraversalEvent) : Prop :=
  ∀ event ∈ events, ∃ state, tree.stateAt event.node = some state ∧
    event.node < tree.locationStates.size ∧
    AccessOwned state kind event.relatedness (tree.protectedNodes.contains event.node) ∧
    Scheduled state kind event.relatedness

theorem events_complete (events : List TraversalEvent) (root : Nat) (kind : AccessKind)
    (tree : NormalTreeState) (distinct : (events.map TraversalEvent.node).Nodup)
    (owned : EventsOwned tree kind events) :
    (sourceNormalEvents tree root kind events).status = .Completed := by
  induction events generalizing tree with
  | nil => unfold_normal_events
  | cons event rest ih =>
    obtain ⟨state,present,valid,nodeOwned,scheduled⟩ := owned event (by simp)
    obtain ⟨next,preserved,step⟩ := event_cons tree root event kind state present valid nodeOwned scheduled
    rw [step]
    simp only [List.map_cons,List.nodup_cons] at distinct
    apply ih _ distinct.2
    intro later member
    obtain ⟨old,oldPresent,oldValid,oldOwned,oldScheduled⟩ := owned later (by simp [member])
    have different : later.node ≠ event.node := by
      intro same
      apply distinct.1
      exact List.mem_map.mpr ⟨later,member,same⟩
    refine ⟨old,?_,?_,oldOwned,oldScheduled⟩
    · rw [stateAt_update_other tree event.node later.node next valid different]
      exact oldPresent
    · simpa using oldValid

/-- Source normal-tree access for arbitrary topology/arrays. The remaining
premises concern only the pure visitor schedule and pointwise initial state;
no source access success is assumed. -/
theorem normal_access_complete (tree : NormalTreeState) (start : Nat)
    (kind : AccessKind) (mode : ChildrenVisitMode)
    (distinct : ((tree.topology.traverse start mode (sourceNormalSkipped tree kind)).2.map
      TraversalEvent.node).Nodup)
    (owned : EventsOwned tree kind
      (tree.topology.traverse start mode (sourceNormalSkipped tree kind)).2) :
    (tree.performAccess start kind mode).status = .Completed := by
  unfold NormalTreeState.performAccess
  exact events_complete _ _ kind tree distinct owned

theorem skipped_iff (tree : NormalTreeState) (kind : AccessKind)
    (index : Nat) (state : LocationState) (present : tree.stateAt index = some state)
    (valid : index < tree.topology.nodes.size) :
    index ∈ sourceNormalSkipped tree kind ↔
      state.skipIfKnownNoop kind .ForeignAccess = .SkipSelfAndChildren := by
  unfold_normal_skips
  simp [List.mem_filter,List.mem_range,present,valid]

end DuplicatePrefix.GeneralBorrowEvents

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowEvents." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved general tree event dependency {dependency}"
