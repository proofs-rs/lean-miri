import duplicate_prefix.GeneralBorrowTraversal
import duplicate_prefix.GeneralBorrowStorage
namespace DuplicatePrefix.GeneralBorrowOwnership
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowPermissions DuplicatePrefix.GeneralBorrowEvents
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

def Pointwise (tree : NormalTreeState) (writable : Nat → Bool) (related : Nat → AccessRelatedness) : Prop :=
  ∀ index, index < tree.locationStates.size → ∃ state, tree.stateAt index = some state ∧
    Required state (writable index) (related index) (tree.protectedNodes.contains index)

theorem update_pointwise (tree : NormalTreeState) (writable : Nat → Bool) (related : Nat → AccessRelatedness)
    (owned : Pointwise tree writable related) (index : Nat) (valid : index < tree.locationStates.size)
    (next : LocationState) (nextOwned : Required next (writable index) (related index) (tree.protectedNodes.contains index)) :
    Pointwise {tree with locationStates := tree.locationStates.set index (some next) valid} writable related := by
  intro position positionValid
  have beforeValid : position < tree.locationStates.size := by simpa using positionValid
  by_cases same : position = index
  · subst position
    exact ⟨next,by simp [NormalTreeState.stateAt,valid],nextOwned⟩
  · obtain ⟨old,present,oldOwned⟩ := owned position beforeValid
    exact ⟨old,(stateAt_update_other tree index position next valid same).trans present,oldOwned⟩

theorem event_cons (tree : NormalTreeState) (root : Nat) (event : TraversalEvent)
    (kind : AccessKind) (state : LocationState) (writable : Bool)
    (present : tree.stateAt event.node = some state) (valid : event.node < tree.locationStates.size)
    (owned : Required state writable event.relatedness (tree.protectedNodes.contains event.node))
    (allowed : writable = false → event.relatedness = .LocalAccess → kind = .Read)
    (scheduled : Scheduled state kind event.relatedness) :
    ∃ next, Required next writable event.relatedness (tree.protectedNodes.contains event.node) ∧
      ∀ rest, sourceNormalEvents tree root kind (event :: rest) =
        let later := sourceNormalEvents {tree with locationStates := tree.locationStates.set event.node (some next) valid} root kind rest
        {later with visited := event :: later.visited} := by
  obtain ⟨recorded,next,transition,record,access,preserved⟩ :=
    (required_visit state writable kind event.relatedness (tree.protectedNodes.contains event.node) allowed owned).resolve_left
      (by rw [scheduled_recurse state kind event.relatedness scheduled]; decide)
  refine ⟨next,preserved,?_⟩
  intro rest
  unfold_normal_events
  simp only [present,record,access,valid,↓reduceDIte]
  rfl

def Recordable (tree : NormalTreeState) (kind : AccessKind) (events : List TraversalEvent) : Prop :=
  ∀ event ∈ events, ∃ state, tree.stateAt event.node = some state ∧
    event.node < tree.locationStates.size ∧ Scheduled state kind event.relatedness

theorem events_preserve (events : List TraversalEvent) (root : Nat) (kind : AccessKind)
    (tree : NormalTreeState) (writable : Nat → Bool) (related : Nat → AccessRelatedness)
    (owned : Pointwise tree writable related) (distinct : (events.map TraversalEvent.node).Nodup)
    (recordable : Recordable tree kind events)
    (relations : ∀ event ∈ events, event.relatedness = related event.node)
    (allowed : ∀ event ∈ events, writable event.node = false → event.relatedness = .LocalAccess → kind = .Read) :
    (sourceNormalEvents tree root kind events).status = .Completed ∧
      Pointwise (sourceNormalEvents tree root kind events).tree writable related := by
  induction events generalizing tree with
  | nil => unfold_normal_events; exact ⟨trivial,owned⟩
  | cons event rest ih =>
    obtain ⟨state,present,valid,scheduled⟩ := recordable event (by simp)
    obtain ⟨old,oldPresent,oldOwned⟩ := owned event.node valid
    have oldEq : old = state := Option.some.inj (oldPresent.symm.trans present)
    subst old
    have relationEq := relations event (by simp)
    have eventOwned : Required state (writable event.node) event.relatedness (tree.protectedNodes.contains event.node) := by
      rw [relationEq]; exact oldOwned
    obtain ⟨next,preserved,step⟩ := event_cons tree root event kind state (writable event.node) present valid eventOwned
      (allowed event (by simp)) scheduled
    have nextOwned := update_pointwise tree writable related owned event.node valid next (by rw [←relationEq]; exact preserved)
    rw [step]
    simp only [List.map_cons,List.nodup_cons] at distinct
    apply ih _ nextOwned distinct.2
    · intro later member
      obtain ⟨old,oldPresent,oldValid,oldScheduled⟩ := recordable later (by simp [member])
      have different : later.node ≠ event.node := by
        intro same
        exact distinct.1 (List.mem_map.mpr ⟨later,member,same⟩)
      exact ⟨old,(stateAt_update_other tree event.node later.node next valid different).trans oldPresent,
        by simpa using oldValid,oldScheduled⟩
    · exact fun later member => relations later (by simp [member])
    · exact fun later member => allowed later (by simp [member])
/-- Read and write ownership preservation on the actual arbitrary-tree
normal operation. Temporary shared leaves may be marked read-only while
mutable ancestors retain the stronger invariant. -/
theorem normal_preserves (tree : NormalTreeState) (forest : GeneralBorrowForest.Forest tree.topology)
    (anchor : Nat) (valid : anchor < tree.topology.nodes.size) (kind : AccessKind) (mode : ChildrenVisitMode)
    (writable : Nat → Bool) (aligned : tree.locationStates.size = tree.topology.nodes.size)
    (owned : Pointwise tree writable (GeneralBorrowAnchor.relation tree anchor))
    (allowed : ∀ index, index < tree.locationStates.size → writable index = false →
      GeneralBorrowAnchor.relation tree anchor index = .LocalAccess → kind = .Read) :
    (tree.performAccess anchor kind mode).status = .Completed ∧
      Pointwise (tree.performAccess anchor kind mode).tree writable (GeneralBorrowAnchor.relation tree anchor) := by
  let schedule := tree.topology.traverse anchor mode (sourceNormalSkipped tree kind)
  have data := GeneralBorrowTraversal.traversal_data tree.topology forest anchor valid mode (sourceNormalSkipped tree kind)
  apply events_preserve schedule.2 schedule.1 kind tree writable (GeneralBorrowAnchor.relation tree anchor) owned data.1
  · intro event member
    have eventValid : event.node < tree.locationStates.size := by rw [aligned]; exact (data.2 event member).1
    obtain ⟨state,present,_⟩ := owned event.node eventValid
    refine ⟨state,present,eventValid,?_⟩
    apply recurse_scheduled
    cases relatedEq : event.relatedness with
    | LocalAccess => rfl
    | ForeignAccess =>
      have notSkipped := GeneralBorrowTopology.traversal_foreign_not_skipped tree.topology
        (sourceNormalSkipped tree kind) anchor mode event member relatedEq
      have noSkip : state.skipIfKnownNoop kind .ForeignAccess ≠ .SkipSelfAndChildren := by
        intro skipped
        exact notSkipped ((skipped_iff tree kind event.node state present (data.2 event member).1).mpr skipped)
      cases skip : state.skipIfKnownNoop kind .ForeignAccess with
      | Recurse => rfl
      | SkipSelfAndChildren => exact False.elim (noSkip skip)
  · exact fun event member => (data.2 event member).2
  · intro event member readOnly localAccess
    apply allowed event.node (by rw [aligned]; exact (data.2 event member).1) readOnly
    exact (data.2 event member).2.symm.trans localAccess

end DuplicatePrefix.GeneralBorrowOwnership

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowOwnership." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved generic ownership dependency {dependency}"
