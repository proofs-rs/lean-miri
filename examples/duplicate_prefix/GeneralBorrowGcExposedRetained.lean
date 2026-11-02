import duplicate_prefix.GeneralBorrowGcEligibilityFacts
import duplicate_prefix.GeneralBorrowGcGuardedWhile
import duplicate_prefix.GeneralBorrowGcRootInvariant

namespace DuplicatePrefix.GeneralBorrowGcExposedRetained
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcGuardedFold
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- All source tags marked exposed are explicitly supplied to actual GC's
liveness vector. This is initial resource metadata, not a successful-GC premise. -/
def ExposedLive (tree : BorrowTree) (live : Array BorTag) : Prop :=
  ∀ index node,tree.nodes.get index = some node → node.isExposed = true → live.contains node.tag = true

def Retained (original current : BorrowTree) : Prop :=
  ∀ index node,original.nodes.get index = some node → node.isExposed = true →
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

private theorem remove (original tree : BorrowTree) (live : Array BorTag) (liveData : ExposedLive original live)
    (index : UniIndex) (eligible : Eligible tree index live) (good : Retained original tree) :
    Retained original (source_remove_useless_node tree index).1 := by
  intro query old originalPresent exposed
  obtain ⟨node,present,tag⟩ := good query old originalPresent exposed
  have different : query ≠ index := by
    intro same
    subst query
    exact live_not_eligible tree index node live present (tag ▸ liveData index old originalPresent exposed) eligible
  refine ⟨node,?_,tag⟩
  cases stored : tree.nodes.get index with
  | none => unfold_source_remove_useless_node;simpa only [stored,Id.run,pure] using present
  | some removed =>
    unfold_source_remove_useless_node
    simpa only [stored,Id.run,pure,GeneralBorrowSparseRemoval.remove_get_other _ index query different] using present

private theorem update (original tree : BorrowTree) (index : UniIndex) (before after : TreeNode)
    (present : tree.nodes.get index = some before) (tag : after.tag = before.tag) (good : Retained original tree) :
    Retained original {tree with nodes := tree.nodes.insert index after} := by
  intro query node originalPresent exposed
  obtain ⟨current,found,sameTag⟩ := good query node originalPresent exposed
  by_cases same : query = index
  · subst query
    have equal := Option.some.inj (present.symm.trans found)
    subst current
    exact ⟨after,GeneralBorrowNodeUpdate.insert_existing_get_same tree.nodes index before after present,tag.trans sameTag⟩
  · exact ⟨current,(GeneralBorrowNodeUpdate.insert_existing_get_other tree.nodes index query before after present same).trans found,sameTag⟩

/-- Every ORIGINAL exposed index genuinely survives FULL production GC with its
original tag, for arbitrary graph/root lists, including error states. The actual
GC eligibility checks are used; no retained-node conclusion is assumed. -/
theorem collect (tree : BorrowTree) (live : Array BorTag) (liveData : ExposedLive tree live) :
    Retained tree (tree.removeUnreachableTags live).tree := by
  apply GeneralBorrowGcRootInvariant.preserves (Retained tree) tree live
    (by intro index node present exposed;exact ⟨node,present,rfl⟩)
  · intro current root initial
    exact GeneralBorrowGcGuardedWhile.preserves (Retained tree) live
      (fun current index eligible good => remove tree current live liveData index eligible good)
      (fun current index old new present tag good => update tree current index old new present tag good)
      current root initial
  · intro current initial
    exact initial

end DuplicatePrefix.GeneralBorrowGcExposedRetained
