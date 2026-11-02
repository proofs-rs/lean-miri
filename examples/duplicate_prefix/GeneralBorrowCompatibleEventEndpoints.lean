import duplicate_prefix.DuplicatePrefixScalarAuthorization
import duplicate_prefix.GeneralBorrowEventTransitionMetadata
namespace DuplicatePrefix.GeneralBorrowCompatibleEventEndpoints
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowEvents GeneralBorrowEventTransitionMetadata GeneralBorrowStorage GeneralBorrowFreshActiveOnClean
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Raw compatibility and SIFA schedule of actual events. No transition or
completion equation occurs in this input predicate. -/
def EventsCompatible (tree : NormalTreeState) (kind : AccessKind) (items : List TraversalEvent) : Prop :=
  ∀ event ∈ items, ∃ state, tree.stateAt event.node = some state ∧ event.node < tree.locationStates.size ∧
    DuplicatePrefixScalarAuthorization.Compatible state kind event.relatedness (tree.protectedNodes.contains event.node) ∧
    Scheduled state kind event.relatedness

/-- Every distinct scheduled owned event's final state is its own actual
permission-transition endpoint. Later visitors cannot overwrite that node.
The operation's completion is derived from EventsOwned, never assumed. -/
theorem events (items : List TraversalEvent) (root : Nat) (kind : AccessKind) (tree : NormalTreeState)
    (distinct : (items.map TraversalEvent.node).Nodup) (owned : EventsCompatible tree kind items) :
    ∀ event ∈ items, Nonempty (Endpoint tree items root kind event) := by
  induction items generalizing tree with
  | nil => intro event member;cases member
  | cons head rest ih =>
    obtain ⟨old,present,valid,compatible,scheduled⟩ := owned head (by simp)
    let recorded := {old with idempotentForeignAccess := (
      IdempotentForeignAccess.recordNew old.idempotentForeignAccess
        (IdempotentForeignAccess.fromAccessAndRelatedness kind head.relatedness))}
    have compatibleRecorded : DuplicatePrefixScalarAuthorization.Compatible recorded kind head.relatedness
        (tree.protectedNodes.contains head.node) := by
      cases kind <;> exact compatible
    have possible : recorded.possible = true := by
      cases kind <;> exact compatible.1
    obtain ⟨next,transition,access⟩ :=
      (DuplicatePrefixScalarAuthorization.compatible_iff recorded kind head.relatedness _ possible).mp compatibleRecorded
    have record : old.recordNewAccess kind head.relatedness = .Recorded recorded := by
      simp only [LocationState.recordNewAccess,scheduled_recurse old kind head.relatedness scheduled,beq_self_eq_true,↓reduceIte]
      rfl
    have endpoints := success_endpoint recorded next transition kind head.relatedness (tree.protectedNodes.contains head.node) access
    have permission := record_permission old recorded kind head.relatedness record
    let updated := {tree with locationStates := tree.locationStates.set head.node (some next) valid}
    have step : sourceNormalEvents tree root kind (head :: rest) =
        {sourceNormalEvents updated root kind rest with visited := head :: (sourceNormalEvents updated root kind rest).visited} := by
      unfold_normal_events
      simp only [present,record,access,valid,↓reduceDIte]
      rfl
    have nodup := List.nodup_cons.mp distinct
    have laterOwned : EventsCompatible updated kind rest := by
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

end DuplicatePrefix.GeneralBorrowCompatibleEventEndpoints
