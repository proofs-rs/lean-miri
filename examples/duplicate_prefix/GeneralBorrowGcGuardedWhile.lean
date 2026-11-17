import duplicate_prefix.GeneralBorrowGcGuardedFold
import duplicate_prefix.GeneralBorrowGcWhileInvariant
namespace DuplicatePrefix.GeneralBorrowGcGuardedWhile
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcWalker DuplicatePrefix.GeneralBorrowGcGuardedFold
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
def Good (P : BorrowTree → Prop) (state : OuterState) : Prop :=
  P state.2.1 ∧ ∀ result, state.1 = some result → P result.tree

def measure (state : OuterState) : Nat := state.2.1.nodes.size*2+2-state.2.2.2

private theorem remove_capacity (tree : BorrowTree) (index : UniIndex) :
    (source_remove_useless_node tree index).1.nodes.size = tree.nodes.size := by
  cases present : tree.nodes.get index with
  | none => unfold_source_remove_useless_node;simp only [present,Id.run,bind,pure]
  | some node =>
    unfold_source_remove_useless_node
    simp only [present,Id.run,bind,pure]
    exact GeneralBorrowSparseRemoval.remove_size tree.nodes index

/-- One exact production GC while step preserves P and decreases the source
cycle-counter bound on every continuing branch. -/
theorem step_preserves (P : BorrowTree → Prop) (live : Array BorTag)
    (removed : ∀ tree index, Eligible tree index live → P tree → P (source_remove_useless_node tree index).1)
    (updated : ∀ tree index oldNode newNode, tree.nodes.get index = some oldNode → newNode.tag = oldNode.tag →
      P tree → P {tree with nodes := tree.nodes.insert index newNode})
    (seed : BorrowTree) (root : UniIndex)
    (state : OuterState) (good : Good P state) :
    (∃ final, outerScan seed root live () state = .done final ∧ Good P final) ∨
    ∃ next, outerScan seed root live () state = .yield next ∧ Good P next ∧ measure next < measure state := by
  rcases state with ⟨returned,current,stack,steps⟩
  simp only [outerScan,pure]
  split
  · rename_i nonempty
    split
    · exact .inl ⟨_,rfl,good.1,fun result same => by cases same;exact good.1⟩
    · rename_i bounded
      split
      · rename_i index nthChild back
        split
        · rename_i node present
          split
          · rename_i hasChild
            split
            · refine .inr ⟨_,rfl,⟨good.1,by simp⟩,?_⟩
              simp only [measure]
              omega
            · exact .inl ⟨_,rfl,good.1,fun result same => by cases same;exact good.1⟩
          · rename_i finished
            fold_gc_child_callback (seed,root,live,index)
            let Q := fun tree : BorrowTree => P tree ∧ tree.nodes.size = current.nodes.size
            have removedQ : ∀ tree index, Eligible tree index live → Q tree → Q (source_remove_useless_node tree index).1 := by
              intro tree index eligible valid
              exact ⟨removed tree index eligible valid.1,(remove_capacity tree index).trans valid.2⟩
            have updatedQ : ∀ tree index oldNode newNode, tree.nodes.get index = some oldNode → newNode.tag = oldNode.tag →
                Q tree → Q {tree with nodes := tree.nodes.insert index newNode} := by
              intro tree index oldNode newNode found tag valid
              exact ⟨updated tree index oldNode newNode found tag valid.1,
                (GeneralBorrowNodeUpdate.insert_existing_size tree.nodes index oldNode newNode found).trans valid.2⟩
            have initial : GeneralBorrowGcChildFold.Good Q (none,current,#[]) := ⟨⟨good.1,rfl⟩,by simp⟩
            have folded := GeneralBorrowGcGuardedFold.fold_preserves Q live removedQ updatedQ seed root index node.children (none,current,#[]) initial
            generalize actual : forIn (m := Id) node.children (none,current,#[]) (GeneralBorrowGcChildFold.childScan seed root live index) = next at folded ⊢
            rcases next with ⟨answer,after,kept⟩
            cases answer with
            | some result =>
              have resultGood := folded.2 result rfl
              exact .inl ⟨_,rfl,folded.1.1,fun other same => by cases same;exact resultGood.1⟩
            | none =>
              simp only [Id.run,bind,pure]
              split
              · rename_i currentNode lookup
                have changed := updated after index currentNode {currentNode with children := kept} lookup rfl folded.1.1
                have capacity := GeneralBorrowNodeUpdate.insert_existing_size after.nodes index currentNode
                  {currentNode with children := kept} lookup
                refine .inr ⟨_,rfl,⟨changed,by simp⟩,?_⟩
                simp only [measure]
                rw [capacity,folded.1.2]
                omega
              · exact .inl ⟨_,rfl,folded.1.1,fun other same => by cases same;exact folded.1.1⟩
        · exact .inl ⟨_,rfl,good.1,fun result same => by cases same;exact good.1⟩
      · exact .inl ⟨_,rfl,good.1,fun result same => by cases same;exact good.1⟩
  · exact .inl ⟨_,rfl,good.1,by simp⟩

/-- The actual postorder GC child walker preserves every predicate stable
under source removal and tag-preserving existing-node updates, including errors. -/
theorem preserves (P : BorrowTree → Prop) (live : Array BorTag)
    (removed : ∀ tree index, Eligible tree index live → P tree → P (source_remove_useless_node tree index).1)
    (updated : ∀ tree index oldNode newNode, tree.nodes.get index = some oldNode → newNode.tag = oldNode.tag →
      P tree → P {tree with nodes := tree.nodes.insert index newNode})
    (tree : BorrowTree) (root : UniIndex) (initial : P tree) :
    P (source_gc_children tree root live).tree := by
  rw [children_equation]
  have maintained := GeneralBorrowLoop.invariant (outerScan tree root live) measure (Good P)
    (step_preserves P live removed updated tree root) (none,tree,#[(root,0)],0) ⟨initial,by simp⟩
  dsimp only
  cases returned : (Lean.Loop.forIn {} (none,tree,#[(root,0)],0) (outerScan tree root live)).1 with
  | some result => simpa only [returned] using maintained.2 result returned
  | none => simpa only [returned] using maintained.1
end DuplicatePrefix.GeneralBorrowGcGuardedWhile
