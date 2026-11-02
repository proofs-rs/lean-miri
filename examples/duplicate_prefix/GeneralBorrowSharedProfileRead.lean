import duplicate_prefix.GeneralBorrowSharedGeneratorProfile
import duplicate_prefix.GeneralBorrowFreshActiveOnClean
namespace DuplicatePrefix.GeneralBorrowSharedProfileRead
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowEvents DuplicatePrefix.GeneralBorrowStorage DuplicatePrefix.GeneralBorrowFreshActiveOnClean
open DuplicatePrefix.GeneralBorrowFreshAnchor
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

def StoredExact (tree : NormalTreeState) (position : Nat) (expected : LocationState) : Prop :=
  tree.locationStates[position]? = some (some expected)

private theorem update_exact (expected : LocationState) (tree : NormalTreeState) (position index : Nat)
    (stored : StoredExact tree position expected) (valid : index < tree.locationStates.size) (state : LocationState)
    (newExact : index = position → state = expected) :
    StoredExact {tree with locationStates := tree.locationStates.set index (some state) valid} position expected := by
  by_cases same : index = position
  · subst index
    exact by simp only [StoredExact,Array.getElem?_set,ite_true,newExact rfl]
  · simpa only [StoredExact,Array.getElem?_set,ite_eq_right same] using stored

/-- Exact stored-state preservation through actual Read processing, including early errors. -/
theorem events_exact (expected : LocationState) (events : List TraversalEvent) (root : Nat) (tree : NormalTreeState) (position : Nat)
    (stored : StoredExact tree position expected)
    (stable : ∀ event ∈ events, event.node = position → ∀ recorded held, expected.recordNewAccess .Read event.relatedness = .Recorded recorded →
      (recorded.performAccess .Read event.relatedness held).resultingState = expected) :
    StoredExact (sourceNormalEvents tree root .Read events).tree position expected := by
  induction events generalizing tree with
  | nil => unfold_normal_events;exact stored
  | cons event rest ih =>
    cases present : tree.stateAt event.node with
    | none => unfold_storage_events;simpa only [present] using stored
    | some state =>
      cases record : state.recordNewAccess .Read event.relatedness with
      | DebugAssertion => unfold_storage_events;simpa only [present,record] using stored
      | Recorded recorded =>
        have newExact : event.node = position →
            (recorded.performAccess .Read event.relatedness (tree.protectedNodes.contains event.node)).resultingState = expected := by
          intro same
          subst position
          have storedAt : tree.locationStates[event.node]? = some (some expected) := stored
          have equal : expected = state := by
            simpa only [NormalTreeState.stateAt,storedAt,Option.some.injEq] using present
          exact stable event (by simp) rfl recorded _ (equal.symm ▸ record)
        cases access : recorded.performAccess .Read event.relatedness (tree.protectedNodes.contains event.node) <;>
          by_cases valid : event.node < tree.locationStates.size
        all_goals unfold_storage_events
        all_goals simp only [present,record,access,valid,↓reduceDIte,LocationState.AccessResult.resultingState]
        all_goals first
          | exact stored
          | exact ih _ (update_exact expected tree position event.node stored valid _ (by simpa only [access,LocationState.AccessResult.resultingState] using newExact)) (fun next member => stable next (by simp [member]))
          | exact update_exact expected tree position event.node stored valid _ (by simpa only [access,LocationState.AccessResult.resultingState] using newExact)

/-- Lift exact-state preservation through actual permission write-back and cache processing. -/
theorem normal_exact (expected : LocationState) (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (source query : UniIndex) (node : TreeNode) (mode : ChildrenVisitMode)
    (present : tree.nodeAt query = some node)
    (storedState : location.perms.get query = some expected)
    (localEvents : ∀ event ∈ ((source_normal_projection tree location protections).topology.traverse source.toNat mode
        (sourceNormalSkipped (source_normal_projection tree location protections) .Read)).2,
      event.node = query.toNat → ∀ recorded held, expected.recordNewAccess .Read event.relatedness = .Recorded recorded →
      (recorded.performAccess .Read event.relatedness held).resultingState = expected) :
    (tree.performNormalAccessAt location source .Read protections mode).location.perms.get query = some expected := by
  have projected : StoredExact (source_normal_projection tree location protections) query.toNat expected := by
    change (source_normal_projection tree location protections).locationStates[query.toNat]? = some (some expected)
    unfold_general_projection
    rw [Array.getElem?_mapIdx]
    obtain ⟨valid,nodeStored⟩ := array_of_node tree query node present
    simp only [Array.getElem?_eq_getElem valid,nodeStored,Option.map_some,index_self,storedState]
  have final := events_exact expected
    ((source_normal_projection tree location protections).topology.traverse source.toNat mode
      (sourceNormalSkipped (source_normal_projection tree location protections) .Read)).2
    ((source_normal_projection tree location protections).topology.traverse source.toNat mode
      (sourceNormalSkipped (source_normal_projection tree location protections) .Read)).1
    (source_normal_projection tree location protections) query.toNat projected localEvents
  change StoredExact ((source_normal_projection tree location protections).performAccess source.toNat .Read mode).tree query.toNat expected at final
  have stored : ((source_normal_projection tree location protections).performAccess source.toNat .Read mode).tree.locationStates[query.toNat]? = some (some expected) := final
  rw [source_normal_perms]
  unfold_clean_write_states
  simp only [Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  change (forIn _ location (source_write_scan _)).perms.get query = some expected
  rw [source_write_list_get]
  have bounded : query.toNat < ((source_normal_projection tree location protections).performAccess source.toNat .Read mode).tree.locationStates.size := by
    exact (Array.getElem?_eq_some_iff.mp stored).1
  have row := (Array.getElem?_eq_some_iff.mp stored).2
  simp [List.mem_range',bounded,row,Option.or]
private theorem unique_stable (recorded : LocationState) (held : Bool)
    (record : GeneralBorrowWildcardLeaf.unique.recordNewAccess .Read .LocalAccess = .Recorded recorded) :
    (recorded.performAccess .Read .LocalAccess held).resultingState = GeneralBorrowWildcardLeaf.unique := by
  have same : recorded = GeneralBorrowWildcardLeaf.unique := by
    change LocationState.RecordAccessResult.Recorded GeneralBorrowWildcardLeaf.unique = .Recorded recorded at record
    exact (LocationState.RecordAccessResult.Recorded.inj record).symm
  subst recorded
  cases held <;> rfl

/-- Normal Read preserves the exact generator profile, including absent
permissions at every vacant sparse slot. All error outcomes are included. -/
theorem normal (input : GeneralBorrowFreshMetadataChildShared.Input) (location : LocationTree)
    (protections : ProtectedTags) (mode : ChildrenVisitMode)
    (profile : GeneralBorrowSharedGeneratorProfile.Profile input.tree location input.parent)
    (relations : ∀ event ∈ ((source_normal_projection input.tree location protections).topology.traverse input.parent.toNat mode
        (sourceNormalSkipped (source_normal_projection input.tree location protections) .Read)).2,
      event.relatedness = if event.node = input.parent.toNat then .LocalAccess else .ForeignAccess) :
    GeneralBorrowSharedGeneratorProfile.Profile input.tree
      (input.tree.performNormalAccessAt location input.parent .Read protections mode).location input.parent := by
  refine ⟨?_,?_,?_⟩
  · apply normal_exact GeneralBorrowWildcardLeaf.unique input.tree location protections input.parent input.parent input.parentNode mode input.parentPresent profile.rootStored
    intro event member same recorded held record
    have localEvent : event.relatedness = .LocalAccess := by simpa only [same,ite_true] using relations event member
    rw [localEvent] at record ⊢
    exact unique_stable recorded held record
  · intro index node present different
    apply normal_exact sharedState input.tree location protections input.parent index node mode present (profile.shared index node present different)
    intro event member same recorded held record
    have distinct : event.node ≠ input.parent.toNat := by
      rw [same]
      exact fun equal => different (GeneralBorrowNodeUpdate.index_injective index input.parent equal)
    have foreign : event.relatedness = .ForeignAccess := by simpa only [ite_eq_right distinct] using relations event member
    rw [foreign] at record
    change LocationState.RecordAccessResult.DebugAssertion = .Recorded recorded at record
    cases record
  · intro index vacant
    exact normal_vacant input.tree location protections input.parent index .Read mode input.depth input.children input.parentNode input.parentPresent vacant (profile.vacant index vacant)
end DuplicatePrefix.GeneralBorrowSharedProfileRead
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowSharedProfileRead.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved shared Read profile dependency {dependency}"
