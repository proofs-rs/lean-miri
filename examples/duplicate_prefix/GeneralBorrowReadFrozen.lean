import duplicate_prefix.GeneralBorrowFreshFrozenTyping
namespace DuplicatePrefix.GeneralBorrowReadFrozen
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowEvents DuplicatePrefix.GeneralBorrowStorage DuplicatePrefix.GeneralBorrowFreshActiveOnClean
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def StoredFrozen (tree : NormalTreeState) (position : Nat) : Prop :=
  ∃ state, tree.locationStates[position]? = some (some state) ∧ state.permission = .Frozen

private theorem record_permission (state recorded : LocationState) (related : AccessRelatedness)
    (record : state.recordNewAccess .Read related = .Recorded recorded) : recorded.permission = state.permission := by
  unfold LocationState.recordNewAccess at record
  split at record
  · cases record;rfl
  · cases record

private theorem access_frozen (state : LocationState) (related : AccessRelatedness) (held : Bool)
    (frozen : state.permission = .Frozen) :
    (state.performAccess .Read related held).resultingState.permission = .Frozen := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases frozen
  cases related <;> cases held <;> cases accessed <;> cases sifa <;> rfl

private theorem update_frozen (tree : NormalTreeState) (position index : Nat)
    (stored : StoredFrozen tree position) (valid : index < tree.locationStates.size) (state : LocationState)
    (newFrozen : index = position → state.permission = .Frozen) :
    StoredFrozen {tree with locationStates := tree.locationStates.set index (some state) valid} position := by
  by_cases same : index = position
  · subst index
    exact ⟨state,by simp,newFrozen rfl⟩
  · obtain ⟨old,present,frozen⟩ := stored
    exact ⟨old,by simpa only [Array.getElem?_set,ite_eq_right same] using present,frozen⟩

/-- A stored Frozen permission stays present and Frozen through every actual
normal Read event, including intermediate failures and lazy materialization. -/
theorem events_frozen (events : List TraversalEvent) (root : Nat) (tree : NormalTreeState) (position : Nat)
    (stored : StoredFrozen tree position) :
    StoredFrozen (sourceNormalEvents tree root .Read events).tree position := by
  induction events generalizing tree with
  | nil => unfold_normal_events;exact stored
  | cons event rest ih =>
    cases present : tree.stateAt event.node with
    | none => unfold_storage_events;simpa only [present] using stored
    | some state =>
      cases record : state.recordNewAccess .Read event.relatedness with
      | DebugAssertion => unfold_storage_events;simpa only [present,record] using stored
      | Recorded recorded =>
        have newFrozen : event.node = position →
            (recorded.performAccess .Read event.relatedness (tree.protectedNodes.contains event.node)).resultingState.permission = .Frozen := by
          intro same
          subst position
          obtain ⟨old,lookup,frozen⟩ := stored
          have equal : old = state := by
            simpa only [NormalTreeState.stateAt,lookup,Option.some.injEq] using present
          apply access_frozen
          exact (record_permission state recorded event.relatedness record).trans (equal ▸ frozen)
        cases access : recorded.performAccess .Read event.relatedness (tree.protectedNodes.contains event.node) <;>
          by_cases valid : event.node < tree.locationStates.size
        all_goals unfold_storage_events
        all_goals simp only [present,record,access,valid,↓reduceDIte,LocationState.AccessResult.resultingState]
        all_goals first
          | exact stored
          | exact ih _ (update_frozen tree position event.node stored valid _ (by simpa only [access,LocationState.AccessResult.resultingState] using newFrozen))
          | exact update_frozen tree position event.node stored valid _ (by simpa only [access,LocationState.AccessResult.resultingState] using newFrozen)

/-- A real normal Read retains any present node's stored Frozen permission.
No success, singleton-root, default-permission or ownership premise is used. -/
theorem normal_frozen (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (source query : UniIndex) (node : TreeNode) (mode : ChildrenVisitMode)
    (present : tree.nodeAt query = some node)
    (frozen : ∃ state, location.perms.get query = some state ∧ state.permission = .Frozen) :
    ∃ state, (tree.performNormalAccessAt location source .Read protections mode).location.perms.get query = some state ∧
      state.permission = .Frozen := by
  obtain ⟨old,oldStored,oldFrozen⟩ := frozen
  have projected : StoredFrozen (source_normal_projection tree location protections) query.toNat := by
    refine ⟨old,?_,oldFrozen⟩
    unfold_general_projection
    rw [Array.getElem?_mapIdx]
    obtain ⟨valid,nodeStored⟩ := array_of_node tree query node present
    simp only [Array.getElem?_eq_getElem valid,nodeStored,Option.map_some,index_self,oldStored]
  have final := events_frozen
    ((source_normal_projection tree location protections).topology.traverse source.toNat mode
      (sourceNormalSkipped (source_normal_projection tree location protections) .Read)).2
    ((source_normal_projection tree location protections).topology.traverse source.toNat mode
      (sourceNormalSkipped (source_normal_projection tree location protections) .Read)).1
    (source_normal_projection tree location protections) query.toNat projected
  change StoredFrozen ((source_normal_projection tree location protections).performAccess source.toNat .Read mode).tree query.toNat at final
  obtain ⟨state,stored,permission⟩ := final
  refine ⟨state,?_,permission⟩
  rw [source_normal_perms]
  unfold_clean_write_states
  simp only [Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  change (forIn _ location (source_write_scan _)).perms.get query = some state
  rw [source_write_list_get]
  have bounded : query.toNat < ((source_normal_projection tree location protections).performAccess source.toNat .Read mode).tree.locationStates.size := by
    exact (Array.getElem?_eq_some_iff.mp stored).1
  have row := (Array.getElem?_eq_some_iff.mp stored).2
  simp [List.mem_range',bounded,row,Option.or]
end DuplicatePrefix.GeneralBorrowReadFrozen
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowReadFrozen." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved frozen Read dependency {dependency}"
