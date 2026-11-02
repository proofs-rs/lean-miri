import duplicate_prefix.GeneralBorrowFreshActiveOnClean
import duplicate_prefix.GeneralBorrowFreshActiveWithin
import duplicate_prefix.S04ReturnReleaseInactive
namespace DuplicatePrefix.S03EmptyPopFactsForeign
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowEvents DuplicatePrefix.GeneralBorrowStorage DuplicatePrefix.GeneralBorrowFreshActiveOnClean
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralBorrowView
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def Inactive (state : LocationState) : Prop := state.accessed = false
def LocationTyped (location : LocationTree) (query : UniIndex) : Prop :=
  ∀ state, location.perms.get query = some state → Inactive state
def DefaultTyped (tree : BorrowTree) (query : UniIndex) : Prop :=
  ∀ node, tree.nodeAt query = some node → node.defaultLocationState.accessed = false

def TreeTyped (tree : BorrowTree) (query : UniIndex) : Prop :=
  DefaultTyped tree query ∧ Every (fun location => LocationTyped location query) tree.locations

private theorem record_typed (state recorded : LocationState) (related : AccessRelatedness) (kind : AccessKind)
    (typed : Inactive state) (record : state.recordNewAccess kind related = .Recorded recorded) : Inactive recorded := by
  unfold LocationState.recordNewAccess at record
  split at record
  · cases record;exact typed
  · cases record
private theorem access_typed (state : LocationState) (held : Bool) (kind : AccessKind)
    (typed : Inactive state) : Inactive (state.performAccess kind .ForeignAccess held).resultingState := by
  rcases state with ⟨permission,accessed,sifa⟩
  have inactive : accessed = false := typed
  subst accessed
  cases permission with
  | ReservedFrz conflicted => cases conflicted <;> cases held <;> cases sifa <;> cases kind <;> rfl
  | Cell | ReservedIM | Unique | Frozen | Disabled => cases held <;> cases sifa <;> cases kind <;> rfl

def StoredTyped (tree : NormalTreeState) (position : Nat) : Prop :=
  ∀ state, tree.locationStates[position]? = some (some state) → Inactive state
def DefaultsTyped (tree : NormalTreeState) (position : Nat) : Prop :=
  ∀ state, tree.defaultStates[position]? = some state → Inactive state

private theorem effective_typed (tree : NormalTreeState) (position : Nat)
    (stored : StoredTyped tree position) (defaults : DefaultsTyped tree position)
    (state : LocationState) (present : tree.stateAt position = some state) : Inactive state := by
  unfold NormalTreeState.stateAt at present
  cases slot : tree.locationStates[position]? with
  | none => simp [slot] at present
  | some entry =>
    cases entry with
    | none => exact defaults state (by simpa only [slot] using present)
    | some value =>
      have same : value = state := by simpa only [slot,Option.some.injEq] using present
      subst value
      exact stored state slot

private theorem update_typed (tree : NormalTreeState) (position index : Nat)
    (stored : StoredTyped tree position) (valid : index < tree.locationStates.size) (state : LocationState)
    (newTyped : index = position → Inactive state) :
    StoredTyped {tree with locationStates := tree.locationStates.set index (some state) valid} position := by
  intro value present
  by_cases same : index = position
  · subst index
    have equal : state = value := by simpa using present
    subst value
    exact newTyped rfl
  · apply stored value
    simpa only [Array.getElem?_set,ite_eq_right same] using present

/-- Actual foreign Read/Write processing retains the inactive bit,
including intermediate error results and lazy-default materialization. -/
theorem events_typed (events : List TraversalEvent) (root : Nat) (tree : NormalTreeState) (position : Nat) (kind : AccessKind)
    (stored : StoredTyped tree position) (defaults : DefaultsTyped tree position)
    (foreignEvents : ∀ event ∈ events,event.node = position → event.relatedness = .ForeignAccess) :
    StoredTyped (sourceNormalEvents tree root kind events).tree position := by
  induction events generalizing tree with
  | nil => unfold_normal_events;exact stored
  | cons event rest ih =>
    cases present : tree.stateAt event.node with
    | none => unfold_storage_events;simpa only [present] using stored
    | some state =>
      cases record : state.recordNewAccess kind event.relatedness with
      | DebugAssertion => unfold_storage_events;simpa only [present,record] using stored
      | Recorded recorded =>
        have newTyped : event.node = position → Inactive (recorded.performAccess kind event.relatedness (tree.protectedNodes.contains event.node)).resultingState := by
          intro same
          subst position
          have related := foreignEvents event (by simp) rfl
          rw [related]
          exact access_typed recorded _ kind (record_typed state recorded event.relatedness kind
            (effective_typed tree event.node stored defaults state present) record)
        cases access : recorded.performAccess kind event.relatedness (tree.protectedNodes.contains event.node) <;>
          by_cases valid : event.node < tree.locationStates.size
        all_goals unfold_storage_events
        all_goals simp only [present,record,access,valid,↓reduceDIte,LocationState.AccessResult.resultingState]
        all_goals first
          | exact stored
          | exact ih _ (update_typed tree position event.node stored valid _ (by simpa only [access,LocationState.AccessResult.resultingState] using newTyped)) defaults (fun next member same => foreignEvents next (by simp [member]) same)
          | exact update_typed tree position event.node stored valid _ (by simpa only [access,LocationState.AccessResult.resultingState] using newTyped)

private theorem projection_stored (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (query : UniIndex) (typed : LocationTyped location query) : StoredTyped (source_normal_projection tree location protections) query.toNat := by
  intro state present
  revert present
  unfold_general_projection
  intro present
  rw [Array.getElem?_mapIdx] at present
  cases slot : tree.nodes.data[query.toNat]? with
  | none => simp [slot] at present
  | some entry =>
    have stored : location.perms.get query = some state := by
      simpa only [slot,Option.map_some,index_self,Option.some.injEq] using present
    exact typed state stored
private theorem projection_default (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (query : UniIndex) (typed : DefaultTyped tree query) : DefaultsTyped (source_normal_projection tree location protections) query.toNat := by
  intro state present
  revert present
  unfold_general_projection
  intro present
  rw [Array.getElem?_map] at present
  cases slot : tree.nodes.data[query.toNat]? with
  | none => simp [slot] at present
  | some entry =>
    cases entry with
    | none =>
      have same : state = ⟨.Disabled,false,.None⟩ := by simpa only [slot,Option.map_some,Option.some.injEq] using present.symm
      subst state
      exact rfl
    | some node =>
      have same : state = node.defaultLocationState := by simpa only [slot,Option.map_some,Option.some.injEq] using present.symm
      subst state
      exact typed node (by simp [BorrowTree.nodeAt,UniValMap.get,slot])

/-- The real normal Read/Write, including permission write-back and exposed-cache
processing, keeps a Inactive/Disabled slot typed without a success assumption. -/
theorem normal (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (source query : UniIndex) (kind : AccessKind) (mode : ChildrenVisitMode)
    (typed : LocationTyped location query)
    (foreignEvents : ∀ event ∈ ((source_normal_projection tree location protections).topology.traverse source.toNat mode
        (sourceNormalSkipped (source_normal_projection tree location protections) kind)).2,event.node = query.toNat → event.relatedness = .ForeignAccess) :
    LocationTyped (tree.performNormalAccessAt location source kind protections mode).location query := by
  have stored := events_typed
    ((source_normal_projection tree location protections).topology.traverse source.toNat mode
      (sourceNormalSkipped (source_normal_projection tree location protections) kind)).2
    ((source_normal_projection tree location protections).topology.traverse source.toNat mode
      (sourceNormalSkipped (source_normal_projection tree location protections) kind)).1
    (source_normal_projection tree location protections) query.toNat kind (projection_stored tree location protections query typed)
      (projection_default tree location protections query (fun _ _ => rfl)) foreignEvents
  change StoredTyped ((source_normal_projection tree location protections).performAccess source.toNat kind mode).tree query.toNat at stored
  intro state present
  rw [source_normal_perms] at present
  revert present
  unfold_clean_write_states
  intro present
  simp only [Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one] at present
  change (forIn _ location (source_write_scan _)).perms.get query = some state at present
  rw [source_write_list_get] at present
  split at present
  · cases optional : ((source_normal_projection tree location protections).performAccess source.toNat kind mode).tree.locationStates[query.toNat]? with
    | none => exact typed state (by simpa [optional,Option.or] using present)
    | some entry =>
      cases entry with
      | none => exact typed state (by simpa [optional,Option.or] using present)
      | some value =>
        have same : value = state := by simpa [optional,Option.or] using present
        subst value
        exact stored state optional
  · exact typed state present
end DuplicatePrefix.S03EmptyPopFactsForeign
