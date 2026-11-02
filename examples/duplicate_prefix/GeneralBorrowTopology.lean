import Lean
import duplicate_prefix.GeneralBorrowEvents
namespace DuplicatePrefix.GeneralBorrowTopology
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open Lean Elab Tactic
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
private def sourceHelper (suffix : String) : CoreM Name := do
  let candidates := (← getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith suffix then some name else none
  match candidates with
  | [name] => pure name
  | _ => throwError "expected actual topology helper {suffix}"
elab "sourceAncestorPath" : term => return mkConst (← sourceHelper ".TraversalTree.ancestorPathAux")
elab "sourceForeignPostorder" : term => return mkConst (← sourceHelper ".TraversalTree.foreignPostorder")
elab "unfold_source_ancestors" : tactic => do
  let aux := mkIdent (← sourceHelper ".TraversalTree.ancestorPathAux")
  let node := mkIdent (← sourceHelper ".TraversalTree.nodeAt")
  evalTactic (← `(tactic| simp only [$aux:ident,$node:ident]))

/-- Pure finite-forest invariant: parent edges remain in bounds and strictly
lower an arbitrary natural rank. No permission or access result occurs here. -/
def ParentRanks (tree : TraversalTree) (rank : Nat → Nat) : Prop :=
  ∀ index (valid : index < tree.nodes.size) parent,
    tree.nodes[index].parent = some parent → parent < tree.nodes.size ∧ rank parent < rank index

theorem ancestors_data (tree : TraversalTree) (rank : Nat → Nat) (ranked : ParentRanks tree rank)
    (fuel current : Nat) (valid : current < tree.nodes.size) :
    (sourceAncestorPath tree fuel current).Nodup ∧
    ∀ ancestor ∈ sourceAncestorPath tree fuel current,
      ancestor < tree.nodes.size ∧ rank ancestor ≤ rank current := by
  induction fuel generalizing current with
  | zero =>
    unfold_source_ancestors
    simp [valid]
  | succ fuel ih =>
    unfold_source_ancestors
    simp only [Array.getElem?_eq_getElem valid,Option.getD_some]
    cases parentEq : tree.nodes[current].parent with
    | none => simp [valid]
    | some parent =>
      have parentData := ranked current valid parent parentEq
      have rest := ih parent parentData.1
      constructor
      · apply List.nodup_cons.mpr
        refine ⟨?_,rest.1⟩
        intro member
        have depth := (rest.2 current member).2
        omega
      · intro ancestor member
        rcases List.mem_cons.mp member with same | later
        · subst ancestor; exact ⟨valid,Nat.le_refl _⟩
        · have inherited := rest.2 ancestor later
          exact ⟨inherited.1, Nat.le_trans inherited.2 (Nat.le_of_lt parentData.2)⟩

theorem ancestor_path_nodup (tree : TraversalTree) (rank : Nat → Nat)
    (ranked : ParentRanks tree rank) (current : Nat) (valid : current < tree.nodes.size) :
    (tree.ancestorPath current).Nodup :=
  (ancestors_data tree rank ranked tree.nodes.size current valid).1
theorem foreign_zero (tree : TraversalTree) (skips : List Nat) (root : Nat) :
    sourceForeignPostorder tree skips 0 root = [] := rfl

theorem foreign_succ (tree : TraversalTree) (skips : List Nat) (fuel root : Nat) :
    sourceForeignPostorder tree skips (fuel+1) root =
      if skips.contains root then [] else
        ((tree.nodes[root]?.getD ⟨none,[]⟩).children.reverse.flatMap
          (sourceForeignPostorder tree skips fuel)) ++ [⟨root,.ForeignAccess⟩] := rfl

/-- Every deferred foreign event is genuinely foreign and was not pruned.
No wellformedness assumption or fixed topology is required. -/
theorem foreign_events_data (tree : TraversalTree) (skips : List Nat) (fuel root : Nat)
    (event : TraversalEvent) (member : event ∈ sourceForeignPostorder tree skips fuel root) :
    event.relatedness = .ForeignAccess ∧ event.node ∉ skips := by
  induction fuel generalizing root with
  | zero => simp [foreign_zero] at member
  | succ fuel ih =>
    rw [foreign_succ] at member
    split at member
    · simp at member
    · rename_i notSkipped
      rcases List.mem_append.mp member with nested | here
      · obtain ⟨child,_,inChild⟩ := List.mem_flatMap.mp nested
        exact ih child inChild
      · have same : event = ⟨root,.ForeignAccess⟩ := by simpa using here
        subst event
        exact ⟨rfl, by simpa using notSkipped⟩

theorem traversal_foreign_not_skipped (tree : TraversalTree) (skips : List Nat)
    (anchor : Nat) (mode : ChildrenVisitMode) (event : TraversalEvent)
    (member : event ∈ (tree.traverse anchor mode skips).2)
    (foreign : event.relatedness = .ForeignAccess) : event.node ∉ skips := by
  simp only [TraversalTree.traverse] at member
  rcases List.mem_append.mp member with localEvent | foreignEvent
  · obtain ⟨node,_,same⟩ := List.mem_map.mp localEvent
    subst event
    cases foreign
  · obtain ⟨root,_,inRoot⟩ := List.mem_flatMap.mp foreignEvent
    exact (foreign_events_data tree skips tree.nodes.size root event inRoot).2

end DuplicatePrefix.GeneralBorrowTopology

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowTopology." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved general topology dependency {dependency}"
