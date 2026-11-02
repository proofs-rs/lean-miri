import duplicate_prefix.GeneralBorrowGcEligibilityFacts
import duplicate_prefix.GeneralBorrowGcGuardedWhile
import duplicate_prefix.GeneralBorrowGcRootInvariant

namespace DuplicatePrefix.GeneralBorrowGcLiveRetained
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcGuardedFold
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Every originally live-tagged node retains its actual sparse index and tag. -/
def Retained (original current : BorrowTree) (live : Array BorTag) : Prop :=
  ∀ index node,original.nodes.get index = some node → live.contains node.tag = true →
    ∃ next,current.nodes.get index = some next ∧ next.tag = node.tag

private theorem live_not_eligible (tree : BorrowTree) (index : UniIndex) (node : TreeNode)
    (live : Array BorTag) (present : tree.nodes.get index = some node) (held : live.contains node.tag = true) :
    ¬ Eligible tree index live := by
  intro eligible
  rcases eligible with useless | replacement
  · revert useless
    unfold_gc_live_rules
    simp only [present,held,Bool.not_true,Bool.and_false,Bool.false_eq_true ]
    exact id
  · have none : gc_replacement tree index live = none := by
      unfold_gc_live_rules
      simp only [present,held,Bool.true_or,ite_true,Id.run,pure]
    exact replacement none

private theorem remove (original tree : BorrowTree) (live : Array BorTag) (index : UniIndex) (eligible : Eligible tree index live) (good : Retained original tree live) :
    Retained original (source_remove_useless_node tree index).1 live := by
  intro query old originalPresent held
  obtain ⟨node,present,tag⟩ := good query old originalPresent held
  have different : query ≠ index := by
    intro same
    subst query
    exact live_not_eligible tree index node live present (tag ▸ held) eligible
  refine ⟨node,?_,tag⟩
  cases stored : tree.nodes.get index with
  | none => unfold_source_remove_useless_node;simpa only [stored,Id.run,pure] using present
  | some removed =>
    unfold_source_remove_useless_node
    simpa only [stored,Id.run,pure,GeneralBorrowSparseRemoval.remove_get_other _ index query different] using present

private theorem update (original tree : BorrowTree) (live : Array BorTag) (index : UniIndex) (before after : TreeNode)
    (present : tree.nodes.get index = some before) (tag : after.tag = before.tag) (good : Retained original tree live) :
    Retained original {tree with nodes := tree.nodes.insert index after} live := by
  intro query node originalPresent held
  obtain ⟨current,found,sameTag⟩ := good query node originalPresent held
  by_cases same : query = index
  · subst query
    have equal := Option.some.inj (present.symm.trans found)
    subst current
    exact ⟨after,GeneralBorrowNodeUpdate.insert_existing_get_same tree.nodes index before after present,tag.trans sameTag⟩
  · exact ⟨current,(GeneralBorrowNodeUpdate.insert_existing_get_other tree.nodes index query before after present same).trans found,sameTag⟩

/-- Actual eligibility guards retain every initially live-tagged source node,
including arbitrary descendants, through full production GC and error prefixes. -/
theorem collect (tree : BorrowTree) (live : Array BorTag) :
    Retained tree (tree.removeUnreachableTags live).tree live := by
  apply GeneralBorrowGcRootInvariant.preserves (fun current => Retained tree current live) tree live
    (by intro index node present held;exact ⟨node,present,rfl⟩)
  · intro current root initial
    exact GeneralBorrowGcGuardedWhile.preserves (fun current => Retained tree current live) live
      (fun current index eligible good => remove tree current live index eligible good)
      (fun current index old new present tag good => update tree current live index old new present tag good)
      current root initial
  · intro current initial
    exact initial
end DuplicatePrefix.GeneralBorrowGcLiveRetained
