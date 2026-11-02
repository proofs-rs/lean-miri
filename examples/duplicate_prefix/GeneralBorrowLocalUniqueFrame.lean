import duplicate_prefix.GeneralBorrowFreshFrozenTyping
import duplicate_prefix.GeneralBorrowRootOnlyNormalCache
namespace DuplicatePrefix.GeneralBorrowLocalUniqueFrame
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowEvents DuplicatePrefix.GeneralBorrowStorage DuplicatePrefix.GeneralBorrowFreshActiveOnClean
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def StoredUnique (tree : NormalTreeState) (position : Nat) : Prop :=
  ∃ state, tree.locationStates[position]? = some (some state) ∧ state.permission = .Unique

private theorem record_permission (state recorded : LocationState) (kind : AccessKind) (related : AccessRelatedness)
    (record : state.recordNewAccess kind related = .Recorded recorded) : recorded.permission = state.permission := by
  unfold LocationState.recordNewAccess at record
  split at record
  · cases record;rfl
  · cases record

private theorem access_unique (state : LocationState) (kind : AccessKind) (held : Bool)
    (unique : state.permission = .Unique) :
    (state.performAccess kind .LocalAccess held).resultingState.permission = .Unique := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases unique
  cases kind <;> cases held <;> cases accessed <;> cases sifa <;> rfl

private theorem update_unique (tree : NormalTreeState) (position index : Nat)
    (stored : StoredUnique tree position) (valid : index < tree.locationStates.size) (state : LocationState)
    (newUnique : index = position → state.permission = .Unique) :
    StoredUnique {tree with locationStates := tree.locationStates.set index (some state) valid} position := by
  by_cases same : index = position
  · subst index
    exact ⟨state,by simp,newUnique rfl⟩
  · obtain ⟨old,present,unique⟩ := stored
    exact ⟨old,by simpa only [Array.getElem?_set,ite_eq_right same] using present,unique⟩

/-- A stored Unique permission stays present and Unique through every actual
normal local Read/Write event, including intermediate failures and lazy materialization. -/
theorem events_unique (events : List TraversalEvent) (kind : AccessKind) (root : Nat) (tree : NormalTreeState) (position : Nat)
    (stored : StoredUnique tree position)
    (localEvents : ∀ event ∈ events, event.node = position → event.relatedness = .LocalAccess) :
    StoredUnique (sourceNormalEvents tree root kind events).tree position := by
  induction events generalizing tree with
  | nil => unfold_normal_events;exact stored
  | cons event rest ih =>
    cases present : tree.stateAt event.node with
    | none => unfold_storage_events;simpa only [present] using stored
    | some state =>
      cases record : state.recordNewAccess kind event.relatedness with
      | DebugAssertion => unfold_storage_events;simpa only [present,record] using stored
      | Recorded recorded =>
        have newUnique : event.node = position →
            (recorded.performAccess kind event.relatedness (tree.protectedNodes.contains event.node)).resultingState.permission = .Unique := by
          intro same
          subst position
          obtain ⟨old,lookup,unique⟩ := stored
          have equal : old = state := by
            simpa only [NormalTreeState.stateAt,lookup,Option.some.injEq] using present
          rw [localEvents event (by simp) rfl]
          apply access_unique
          exact (record_permission state recorded kind event.relatedness record).trans (equal ▸ unique)
        cases access : recorded.performAccess kind event.relatedness (tree.protectedNodes.contains event.node) <;>
          by_cases valid : event.node < tree.locationStates.size
        all_goals unfold_storage_events
        all_goals simp only [present,record,access,valid,↓reduceDIte,LocationState.AccessResult.resultingState]
        all_goals first
          | exact stored
          | exact ih _ (update_unique tree position event.node stored valid _ (by simpa only [access,LocationState.AccessResult.resultingState] using newUnique)) (fun next member equal => localEvents next (by simp [member]) equal)
          | exact update_unique tree position event.node stored valid _ (by simpa only [access,LocationState.AccessResult.resultingState] using newUnique)

/-- A real normal local Read/Write retains any present node's stored Unique permission.
No success, singleton-root, default-permission or ownership premise is used. -/
theorem normal_unique (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) (kind : AccessKind)
    (source query : UniIndex) (node : TreeNode) (mode : ChildrenVisitMode)
    (present : tree.nodeAt query = some node)
    (unique : ∃ state, location.perms.get query = some state ∧ state.permission = .Unique)
    (localEvents : ∀ event ∈ ((source_normal_projection tree location protections).topology.traverse source.toNat mode
        (sourceNormalSkipped (source_normal_projection tree location protections) kind)).2,
      event.node = query.toNat → event.relatedness = .LocalAccess) :
    ∃ state, (tree.performNormalAccessAt location source kind protections mode).location.perms.get query = some state ∧
      state.permission = .Unique := by
  obtain ⟨old,oldStored,oldUnique⟩ := unique
  have projected : StoredUnique (source_normal_projection tree location protections) query.toNat := by
    refine ⟨old,?_,oldUnique⟩
    unfold_general_projection
    rw [Array.getElem?_mapIdx]
    obtain ⟨valid,nodeStored⟩ := array_of_node tree query node present
    simp only [Array.getElem?_eq_getElem valid,nodeStored,Option.map_some,index_self,oldStored]
  have final := events_unique
    ((source_normal_projection tree location protections).topology.traverse source.toNat mode
      (sourceNormalSkipped (source_normal_projection tree location protections) kind)).2
    kind ((source_normal_projection tree location protections).topology.traverse source.toNat mode
      (sourceNormalSkipped (source_normal_projection tree location protections) kind)).1
    (source_normal_projection tree location protections) query.toNat projected localEvents
  change StoredUnique ((source_normal_projection tree location protections).performAccess source.toNat kind mode).tree query.toNat at final
  obtain ⟨state,stored,permission⟩ := final
  refine ⟨state,?_,permission⟩
  rw [source_normal_perms]
  unfold_clean_write_states
  simp only [Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  change (forIn _ location (source_write_scan _)).perms.get query = some state
  rw [source_write_list_get]
  have bounded : query.toNat < ((source_normal_projection tree location protections).performAccess source.toNat kind mode).tree.locationStates.size := by
    exact (Array.getElem?_eq_some_iff.mp stored).1
  have row := (Array.getElem?_eq_some_iff.mp stored).2
  simp [List.mem_range',bounded,row,Option.or]
end DuplicatePrefix.GeneralBorrowLocalUniqueFrame
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowLocalUniqueFrame." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved unique Read dependency {dependency}"
