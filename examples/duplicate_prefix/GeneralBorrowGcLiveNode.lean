import duplicate_prefix.GeneralBorrowGcGuardedWhile
import duplicate_prefix.GeneralBorrowGcRootInvariant

namespace DuplicatePrefix.GeneralBorrowGcLiveNode
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcWalker DuplicatePrefix.GeneralBorrowGcGuardedFold
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

open Lean Elab Tactic in
elab "unfold_gc_live_rules" : tactic => do
  let names ← [".BorrowTree.nodeIsUseless", ".BorrowTree.replacementChild?"].mapM fun (suffix : String) => do
    let found := (←getEnv).constants.toList.filterMap fun (name,_) =>
      if name.toString.endsWith suffix then some name else none
    match found with
    | [name] => pure (mkIdent name)
    | _ => throwError "expected pinned GC eligibility rule"
  let names := names.toArray
  evalTactic (← `(tactic| simp only [$[$names:ident],*]))

/-- Both real deletion branches reject a tag explicitly retained by the caller. -/
theorem not_eligible (tree : BorrowTree) (index : UniIndex) (node : TreeNode)
    (live : Array BorTag) (present : tree.nodes.get index = some node)
    (held : live.contains node.tag = true) : ¬ Eligible tree index live := by
  have leaf : gc_useless tree index live = false := by
    unfold_gc_live_rules
    simp only [present,held,Bool.not_true,Bool.and_false]
  have collapse : gc_replacement tree index live = none := by
    unfold_gc_live_rules
    simp only [present,held,Bool.true_or,↓reduceIte,Id.run,bind,pure]
  intro eligible
  rcases eligible with impossible | impossible
  · rw [leaf] at impossible
    cases impossible
  · exact impossible collapse

/-- A live node remains at its original sparse index, with the same tag.
Parent/child metadata are deliberately allowed to change. -/
def Retained (index : UniIndex) (tag : BorTag) (tree : BorrowTree) : Prop :=
  ∃ node, tree.nodes.get index = some node ∧ node.tag = tag

theorem remove_preserves (index : UniIndex) (tag : BorTag) (live : Array BorTag)
    (held : live.contains tag = true) (tree : BorrowTree) (removed : UniIndex)
    (eligible : Eligible tree removed live) (good : Retained index tag tree) :
    Retained index tag (source_remove_useless_node tree removed).1 := by
  obtain ⟨node,present,sameTag⟩ := good
  have different : index ≠ removed := by
    intro equal
    subst removed
    exact not_eligible tree index node live present (sameTag ▸ held) eligible
  cases stored : tree.nodes.get removed with
  | none =>
    unfold_source_remove_useless_node
    simpa only [stored,Id.run,bind,pure] using (show Retained index tag tree from ⟨node,present,sameTag⟩)
  | some old =>
    unfold_source_remove_useless_node
    simp only [stored,Id.run,bind,pure]
    exact ⟨node,(GeneralBorrowSparseRemoval.remove_get_other tree.nodes removed index different).trans present,sameTag⟩

theorem update_preserves (index : UniIndex) (tag : BorTag) (tree : BorrowTree)
    (changed : UniIndex) (oldNode newNode : TreeNode) (present : tree.nodes.get changed = some oldNode)
    (sameTag : newNode.tag = oldNode.tag) (good : Retained index tag tree) :
    Retained index tag {tree with nodes := tree.nodes.insert changed newNode} := by
  obtain ⟨node,lookup,tagged⟩ := good
  by_cases same : index = changed
  · subst changed
    have equal : node = oldNode := Option.some.inj (lookup.symm.trans present)
    exact ⟨newNode,GeneralBorrowNodeUpdate.insert_existing_get_same tree.nodes index oldNode newNode present,
      sameTag.trans (equal ▸ tagged)⟩
  · exact ⟨node,(GeneralBorrowNodeUpdate.insert_existing_get_other tree.nodes changed index oldNode newNode present same).trans lookup,tagged⟩

/-- Full production GC retains each explicitly live node's index and tag,
including partial error states. This does not assert GC success or graph safety. -/
theorem preserves (tree : BorrowTree) (index : UniIndex) (tag : BorTag) (live : Array BorTag)
    (held : live.contains tag = true) (good : Retained index tag tree) :
    Retained index tag (tree.removeUnreachableTags live).tree := by
  apply GeneralBorrowGcRootInvariant.preserves (Retained index tag) tree live good
  · intro current root initial
    exact GeneralBorrowGcGuardedWhile.preserves (Retained index tag) live
      (fun current removed eligible initial => remove_preserves index tag live held current removed eligible initial)
      (fun current changed oldNode newNode present same initial =>
        update_preserves index tag current changed oldNode newNode present same initial)
      current root initial
  · intro current initial
    exact initial

end DuplicatePrefix.GeneralBorrowGcLiveNode
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowGcLiveNode.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved GC live-node dependency {dependency}"
