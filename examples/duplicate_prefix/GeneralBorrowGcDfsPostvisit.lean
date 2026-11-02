import duplicate_prefix.GeneralBorrowGcDfsControl

namespace DuplicatePrefix.GeneralBorrowGcDfsPostvisit
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcWalker DuplicatePrefix.GeneralBorrowGcChildFold
open DuplicatePrefix.GeneralBorrowGcDfsStage
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- An actual postvisit either propagates the real callback result with its
staged data intact, or rewrites the parent's kept-child list and marks it
completed. The lookup cannot fail: no unprocessed original node was mutated. -/
theorem step (original seed tree : BorrowTree) (processed : List UniIndex)
    (root index : UniIndex) (node : TreeNode) (live : Array BorTag)
    (stack : Array (UniIndex × Nat)) (cursor steps : Nat)
    (stage : Stage original processed tree) (unprocessed : index ∉ processed)
    (present : original.nodes.get index = some node) (finished : ¬ cursor < node.children.size)
    (children : ∀ child ∈ node.children.toList, child ∈ processed)
    (budget : steps+1 ≤ tree.nodes.size*2+1) :
    (∃ after, outerScan seed root live () (none,tree,stack.push (index,cursor),steps) =
        .yield (none,after,stack,steps+1) ∧ Stage original (index::processed) after) ∨
    (∃ result after, outerScan seed root live () (none,tree,stack.push (index,cursor),steps) =
        .done (some result,after,stack.push (index,cursor),steps+1) ∧ Stage original processed result.tree) := by
  have currentPresent := (stage.outside index unprocessed).trans present
  have equation := GeneralBorrowGcDfsControl.finish_equation seed tree root index node live stack cursor steps
    currentPresent finished budget
  have good := GeneralBorrowGcDfsChildStage.fold original seed processed node.children.toList root index live children
    (none,tree,#[]) ⟨stage,by simp,by simp⟩
  rw [←Array.forIn_toList] at equation
  generalize actual : forIn (m := Id) node.children.toList (none,tree,#[]) (childScan seed root live index) = folded at equation good
  rcases folded with ⟨returned,after,kept⟩
  cases returned with
  | some result =>
    exact .inr ⟨result,after,equation,good.2.2 result rfl⟩
  | none =>
    have afterPresent := (good.1.outside index unprocessed).trans present
    simp only [afterPresent] at equation
    exact .inl ⟨_,equation,GeneralBorrowGcDfsStage.finish original after processed index node afterPresent kept good.2.1 good.1⟩
end DuplicatePrefix.GeneralBorrowGcDfsPostvisit
