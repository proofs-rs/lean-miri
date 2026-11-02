import duplicate_prefix.GeneralBorrowFreshActiveOnClean
import duplicate_prefix.GeneralBorrowFreshActiveWithin
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingForeignReadQuiet
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowEvents DuplicatePrefix.GeneralBorrowStorage DuplicatePrefix.GeneralBorrowFreshActiveOnClean
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralBorrowView
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def Quiet (state : LocationState) : Prop := state.accessed = false ∨ state.permission = .Cell
def LocationTyped (location : LocationTree) (query : UniIndex) : Prop :=
  ∀ state, location.perms.get query = some state → Quiet state
def DefaultTyped (tree : BorrowTree) (query : UniIndex) : Prop :=
  ∀ node, tree.nodeAt query = some node → Quiet node.defaultLocationState

def TreeTyped (tree : BorrowTree) (query : UniIndex) : Prop :=
  DefaultTyped tree query ∧ Every (fun location => LocationTyped location query) tree.locations

private theorem record_typed (state recorded : LocationState) (related : AccessRelatedness)
    (typed : Quiet state) (record : state.recordNewAccess .Read related = .Recorded recorded) : Quiet recorded := by
  unfold LocationState.recordNewAccess at record
  split at record
  · cases record;exact typed
  · cases record
private theorem access_typed (state : LocationState) (held : Bool)
    (typed : Quiet state) : Quiet (state.performAccess .Read .ForeignAccess held).resultingState := by
  rcases state with ⟨permission,accessed,sifa⟩
  rcases typed with inactive | cell
  · change accessed = false at inactive
    subst accessed
    cases permission with
    | ReservedFrz conflicted => cases conflicted <;> cases held <;> cases sifa <;> exact Or.inl rfl
    | Cell | ReservedIM | Unique | Frozen | Disabled => cases held <;> cases sifa <;> exact Or.inl rfl
  · change permission = .Cell at cell
    subst permission
    cases accessed <;> cases held <;> cases sifa <;> exact Or.inr rfl

def StoredTyped (tree : NormalTreeState) (position : Nat) : Prop :=
  ∀ state, tree.locationStates[position]? = some (some state) → Quiet state
def DefaultsTyped (tree : NormalTreeState) (position : Nat) : Prop :=
  ∀ state, tree.defaultStates[position]? = some state → Quiet state

private theorem effective_typed (tree : NormalTreeState) (position : Nat)
    (stored : StoredTyped tree position) (defaults : DefaultsTyped tree position)
    (state : LocationState) (present : tree.stateAt position = some state) : Quiet state := by
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
    (newTyped : index = position → Quiet state) :
    StoredTyped {tree with locationStates := tree.locationStates.set index (some state) valid} position := by
  intro value present
  by_cases same : index = position
  · subst index
    have equal : state = value := by simpa using present
    subst value
    exact newTyped rfl
  · apply stored value
    simpa only [Array.getElem?_set,ite_eq_right same] using present

/-- Actual abstract foreign Read processing keeps inactive-or-Cell stored states,
including intermediate error results and lazy-default materialization. -/
theorem events_typed (events : List TraversalEvent) (root : Nat) (tree : NormalTreeState) (position : Nat)
    (stored : StoredTyped tree position) (defaults : DefaultsTyped tree position)
    (foreignEvents : ∀ event ∈ events,event.node = position → event.relatedness = .ForeignAccess) :
    StoredTyped (sourceNormalEvents tree root .Read events).tree position := by
  induction events generalizing tree with
  | nil => unfold_normal_events;exact stored
  | cons event rest ih =>
    cases present : tree.stateAt event.node with
    | none => unfold_storage_events;simpa only [present] using stored
    | some state =>
      cases record : state.recordNewAccess .Read event.relatedness with
      | DebugAssertion => unfold_storage_events;simpa only [present,record] using stored
      | Recorded recorded =>
        have newTyped : event.node = position → Quiet (recorded.performAccess .Read event.relatedness (tree.protectedNodes.contains event.node)).resultingState := by
          intro same
          subst position
          have related := foreignEvents event (by simp) rfl
          rw [related]
          exact access_typed recorded _ (record_typed state recorded event.relatedness
            (effective_typed tree event.node stored defaults state present) record)
        cases access : recorded.performAccess .Read event.relatedness (tree.protectedNodes.contains event.node) <;>
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
      exact Or.inl rfl
    | some node =>
      have same : state = node.defaultLocationState := by simpa only [slot,Option.map_some,Option.some.injEq] using present.symm
      subst state
      exact typed node (by simp [BorrowTree.nodeAt,UniValMap.get,slot])

/-- The real normal Read, including permission write-back, retains a quiet query
when all its actual events are foreign. No success premise is assumed. -/
theorem normal (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (source query : UniIndex) (mode : ChildrenVisitMode)
    (typed : LocationTyped location query)
    (foreignEvents : ∀ event ∈ ((source_normal_projection tree location protections).topology.traverse source.toNat mode
        (sourceNormalSkipped (source_normal_projection tree location protections) .Read)).2,event.node = query.toNat → event.relatedness = .ForeignAccess) :
    LocationTyped (tree.performNormalAccessAt location source .Read protections mode).location query := by
  have stored := events_typed
    ((source_normal_projection tree location protections).topology.traverse source.toNat mode
      (sourceNormalSkipped (source_normal_projection tree location protections) .Read)).2
    ((source_normal_projection tree location protections).topology.traverse source.toNat mode
      (sourceNormalSkipped (source_normal_projection tree location protections) .Read)).1
    (source_normal_projection tree location protections) query.toNat (projection_stored tree location protections query typed)
      (projection_default tree location protections query (fun _ _ => Or.inl rfl)) foreignEvents
  change StoredTyped ((source_normal_projection tree location protections).performAccess source.toNat .Read mode).tree query.toNat at stored
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
  · cases optional : ((source_normal_projection tree location protections).performAccess source.toNat .Read mode).tree.locationStates[query.toNat]? with
    | none => exact typed state (by simpa [optional,Option.or] using present)
    | some entry =>
      cases entry with
      | none => exact typed state (by simpa [optional,Option.or] using present)
      | some value =>
        have same : value = state := by simpa [optional,Option.or] using present
        subst value
        exact stored state optional
  · exact typed state present
end DuplicatePrefix.GeneralBorrowProtectedSiblingForeignReadQuiet
