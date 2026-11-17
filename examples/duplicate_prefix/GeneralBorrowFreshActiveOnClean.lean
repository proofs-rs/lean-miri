import duplicate_prefix.GeneralBorrowRangePreserves
import duplicate_prefix.GeneralBorrowNodeUpdate
namespace DuplicatePrefix.GeneralBorrowFreshActiveOnClean
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowEvents DuplicatePrefix.GeneralBorrowStorage
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

open Lean Elab Tactic in
private def helper (suffix : String) : CoreM Name := do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith suffix then some name else none
  match names with
  | [name] => pure name
  | _ => throwError "expected RangePreserves storage helper {suffix}"
open Lean Elab Tactic in
elab "source_write_states" : term => return mkConst (←helper ".GeneralBorrowRangePreserves.writeStates")
open Lean Elab Tactic in
elab "source_write_scan" : term => return mkConst (←helper ".GeneralBorrowRangePreserves.writeScan")
open Lean Elab Tactic in
elab "source_write_list_get" : term => return mkConst (←helper ".GeneralBorrowRangePreserves.writeList_get")
open Lean Elab Tactic in
elab "source_normal_perms" : term => return mkConst (←helper ".GeneralBorrowRangePreserves.normal_location_perms")
open Lean Elab Tactic in
elab "unfold_clean_write_states" : tactic => do
  let name := mkIdent (←helper ".GeneralBorrowRangePreserves.writeStates")
  evalTactic (← `(tactic| unfold $name:ident))

/-- An unvisited normal slot retains its exact optional stored state, including
on early access errors. This is a storage fact, not a successful-access premise. -/
theorem events_unvisited (events : List TraversalEvent) (root : Nat) (kind : AccessKind)
    (tree : NormalTreeState) (position : Nat)
    (outside : ∀ event ∈ events, event.node ≠ position) :
    (sourceNormalEvents tree root kind events).tree.locationStates[position]? = tree.locationStates[position]? := by
  induction events generalizing tree with
  | nil => unfold_normal_events
  | cons event rest ih =>
    have different := outside event (by simp)
    have restOutside : ∀ later ∈ rest, later.node ≠ position := fun later member => outside later (by simp [member])
    cases present : tree.stateAt event.node with
    | none => unfold_storage_events;simp only [present]
    | some state =>
      cases record : state.recordNewAccess kind event.relatedness with
      | DebugAssertion => unfold_storage_events;simp only [present,record]
      | Recorded recorded =>
        cases access : recorded.performAccess kind event.relatedness (tree.protectedNodes.contains event.node) <;>
          by_cases valid : event.node < tree.locationStates.size
        all_goals unfold_storage_events
        all_goals simp only [present,record,access,valid,↓reduceDIte,LocationState.AccessResult.resultingState]
        all_goals first
          | rfl
          | simpa only [Array.getElem?_set,ite_eq_right different] using ih
              {tree with locationStates := tree.locationStates.set event.node (some _) valid} restOutside
          | simp only [Array.getElem?_set,ite_eq_right different]

/-- Materialization and the actual subsequent exposed-cache loop cannot create
an absent slot if the abstract result leaves that optional state absent. -/
theorem normal_from_optional (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor query : UniIndex) (kind : AccessKind) (mode : ChildrenVisitMode)
    (clean : location.perms.get query = none)
    (optional : (((source_normal_projection tree location protections).performAccess anchor.toNat kind mode).tree.locationStates[query.toNat]?).getD none = none) :
    (tree.performNormalAccessAt location anchor kind protections mode).location.perms.get query = none := by
  rw [source_normal_perms]
  unfold_clean_write_states
  simp only [Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  change (forIn _ location (source_write_scan _)).perms.get query = none
  rw [source_write_list_get]
  split <;> simp only [optional,clean,Option.or_none]

/-- An append slot lies beyond every abstract state written by normal access.
No ownership or successful-operation hypothesis is needed for this fact. -/
theorem normal_append (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor query : UniIndex) (kind : AccessKind) (mode : ChildrenVisitMode)
    (atEnd : tree.nodes.data.size ≤ query.toNat) (clean : location.perms.get query = none) :
    (tree.performNormalAccessAt location anchor kind protections mode).location.perms.get query = none := by
  apply normal_from_optional tree location protections anchor query kind mode clean
  have same := events_storage
    ((source_normal_projection tree location protections).topology.traverse anchor.toNat mode
      (sourceNormalSkipped (source_normal_projection tree location protections) kind)).2
    ((source_normal_projection tree location protections).topology.traverse anchor.toNat mode
      (sourceNormalSkipped (source_normal_projection tree location protections) kind)).1
    kind (source_normal_projection tree location protections)
  have sizes : ((source_normal_projection tree location protections).performAccess anchor.toNat kind mode).tree.locationStates.size = tree.nodes.data.size :=
    same.2.2.2.trans (projection_sizes tree location protections).1
  rw [Array.getElem?_eq_none (by omega)]
  rfl

/-- A vacant reused slot cannot occur in the actual normal visitor schedule:
every scheduled node has a concrete stored TreeNode. Its old absence therefore
survives the abstract operation and the real permission write-back. -/
theorem normal_vacant (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor query : UniIndex) (kind : AccessKind) (mode : ChildrenVisitMode)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (vacant : tree.nodes.get query = none) (clean : location.perms.get query = none) :
    (tree.performNormalAccessAt location anchor kind protections mode).location.perms.get query = none := by
  apply normal_from_optional tree location protections anchor query kind mode clean
  have outside : ∀ event ∈ ((source_normal_projection tree location protections).topology.traverse anchor.toNat mode
      (sourceNormalSkipped (source_normal_projection tree location protections) kind)).2, event.node ≠ query.toNat := by
    intro event member equal
    obtain ⟨index,node,converted,indexEq,present⟩ := GeneralBorrowGraph.visited_present tree location protections
      depth children anchor anchorNode anchorPresent kind mode event member
    have same : index = query := GeneralBorrowNodeUpdate.index_injective index query (indexEq.trans equal)
    subst index
    rw [show tree.nodeAt query = none from vacant] at present
    cases present
  have unchanged := events_unvisited
    ((source_normal_projection tree location protections).topology.traverse anchor.toNat mode
      (sourceNormalSkipped (source_normal_projection tree location protections) kind)).2
    ((source_normal_projection tree location protections).topology.traverse anchor.toNat mode
      (sourceNormalSkipped (source_normal_projection tree location protections) kind)).1
    kind (source_normal_projection tree location protections) query.toNat outside
  change ((((source_normal_projection tree location protections).performAccess anchor.toNat kind mode).tree.locationStates[query.toNat]?).getD none) = none
  change (((source_normal_projection tree location protections).performAccess anchor.toNat kind mode).tree.locationStates[query.toNat]?) =
    (source_normal_projection tree location protections).locationStates[query.toNat]? at unchanged
  rw [unchanged]
  unfold_general_projection
  rw [Array.getElem?_mapIdx]
  cases cell : tree.nodes.data[query.toNat]? with
  | none => rfl
  | some entry => simp only [cell,Option.map_some,index_self,clean,Option.getD_some]
end DuplicatePrefix.GeneralBorrowFreshActiveOnClean
