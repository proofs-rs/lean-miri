import duplicate_prefix.GeneralBorrowEvents
namespace DuplicatePrefix.GeneralBorrowStorage
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowEvents
open Lean Elab Tactic
elab "unfold_storage_events" : tactic => do
  let names ← [".NormalTreeState.processEvents", ".NormalTreeState.setState"].mapM fun (suffix : String) => do
    let candidates := (← getEnv).constants.toList.filterMap fun (name,_) =>
      if name.toString.endsWith suffix then some name else none
    match candidates with
    | [name] => pure (mkIdent name)
    | _ => throwError "expected actual source storage helper {suffix}"
  let names := names.toArray
  evalTactic (← `(tactic| simp only [$[$names:ident],*] at *))
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

def SameStorage (before after : NormalTreeState) : Prop :=
  after.topology = before.topology ∧ after.defaultStates = before.defaultStates ∧
  after.protectedNodes = before.protectedNodes ∧ after.locationStates.size = before.locationStates.size

theorem events_storage (events : List TraversalEvent) (root : Nat) (kind : AccessKind)
    (tree : NormalTreeState) : SameStorage tree (sourceNormalEvents tree root kind events).tree := by
  induction events generalizing tree with
  | nil => unfold_normal_events; exact ⟨rfl,rfl,rfl,rfl⟩
  | cons event rest ih =>
    cases present : tree.stateAt event.node with
    | none => unfold_normal_events; simp only [present]; exact ⟨rfl,rfl,rfl,rfl⟩
    | some old =>
      cases record : old.recordNewAccess kind event.relatedness with
      | DebugAssertion => unfold_normal_events; simp only [present,record]; exact ⟨rfl,rfl,rfl,rfl⟩
      | Recorded recorded =>
        cases access : recorded.performAccess kind event.relatedness (tree.protectedNodes.contains event.node) <;>
          by_cases valid : event.node < tree.locationStates.size
        all_goals unfold_normal_events
        all_goals simp only [present,record,access,valid,↓reduceDIte,LocationState.AccessResult.resultingState]
        all_goals try (solve | simp [SameStorage,Array.size_set])
        all_goals simpa only [SameStorage,Array.size_set] using (ih
          {tree with locationStates := tree.locationStates.set event.node (some _) valid})
theorem stateAt_total (tree : NormalTreeState) (aligned : tree.defaultStates.size = tree.locationStates.size)
    (index : Nat) (valid : index < tree.locationStates.size) : ∃ state, tree.stateAt index = some state := by
  unfold NormalTreeState.stateAt
  rw [Array.getElem?_eq_getElem valid]
  cases state : tree.locationStates[index] with
  | some value => exact ⟨value,rfl⟩
  | none =>
    have defaultValid : index < tree.defaultStates.size := by omega
    exact ⟨tree.defaultStates[index],Array.getElem?_eq_getElem defaultValid⟩

theorem events_total (events : List TraversalEvent) (root : Nat) (kind : AccessKind)
    (tree : NormalTreeState) (aligned : tree.defaultStates.size = tree.locationStates.size)
    (index : Nat) (valid : index < tree.locationStates.size) :
    ∃ state, (sourceNormalEvents tree root kind events).tree.stateAt index = some state := by
  have same := events_storage events root kind tree
  apply stateAt_total
  · rw [same.2.1,same.2.2.2]
    exact aligned
  · rw [same.2.2.2]
    exact valid

theorem events_visited (events : List TraversalEvent) (root : Nat) (kind : AccessKind)
    (tree : NormalTreeState) (completed : (sourceNormalEvents tree root kind events).status = .Completed) :
    (sourceNormalEvents tree root kind events).visited = events := by
  induction events generalizing tree with
  | nil => unfold_normal_events
  | cons event rest ih =>
    cases present : tree.stateAt event.node with
    | none => unfold_storage_events; simp only [present] at completed; cases completed
    | some old =>
      cases record : old.recordNewAccess kind event.relatedness with
      | DebugAssertion => unfold_storage_events; simp only [present,record] at completed; cases completed
      | Recorded recorded =>
        cases access : recorded.performAccess kind event.relatedness (tree.protectedNodes.contains event.node) <;>
          by_cases valid : event.node < tree.locationStates.size
        all_goals unfold_storage_events
        all_goals simp only [present,record,access,valid,↓reduceDIte,LocationState.AccessResult.resultingState] at completed ⊢
        all_goals first
          | cases completed
          | exact congrArg (List.cons event) (ih _ completed)

theorem events_root (events : List TraversalEvent) (root : Nat) (kind : AccessKind)
    (tree : NormalTreeState) : (sourceNormalEvents tree root kind events).root = root := by
  induction events generalizing tree with
  | nil => unfold_normal_events
  | cons event rest ih =>
    cases present : tree.stateAt event.node with
    | none => unfold_normal_events; simp only [present]
    | some old =>
      cases record : old.recordNewAccess kind event.relatedness with
      | DebugAssertion => unfold_normal_events; simp only [present,record]
      | Recorded recorded =>
        cases access : recorded.performAccess kind event.relatedness (tree.protectedNodes.contains event.node) <;>
          by_cases valid : event.node < tree.locationStates.size
        all_goals unfold_normal_events
        all_goals simp only [present,record,access,valid,↓reduceDIte,LocationState.AccessResult.resultingState]
        all_goals first | rfl | exact ih _

end DuplicatePrefix.GeneralBorrowStorage

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowStorage." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved general storage dependency {dependency}"
