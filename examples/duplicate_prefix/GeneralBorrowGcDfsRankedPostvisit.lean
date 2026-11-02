import duplicate_prefix.GeneralBorrowGcDfsControl
import duplicate_prefix.GeneralBorrowGcRankedChildFold

namespace DuplicatePrefix.GeneralBorrowGcDfsRankedPostvisit
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcWalker DuplicatePrefix.GeneralBorrowGcChildFold
open DuplicatePrefix.GeneralBorrowGcDfsStage DuplicatePrefix.GeneralBorrowGcStrictChildren
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- A completed original subtree's real postvisit ALWAYS yields successfully:
strict ranks derive child-fold success, while staged unprocessed metadata derive
the parent's postfold lookup. The source counter bound remains a data budget. -/
theorem step (rank : UniIndex → Nat) (original seed tree : BorrowTree) (processed : List UniIndex)
    (root index : UniIndex) (node : TreeNode) (live : Array BorTag)
    (stack : Array (UniIndex × Nat)) (cursor steps : Nat)
    (stage : Stage original processed tree) (ranked : Ranked rank tree) (unprocessed : index ∉ processed)
    (present : original.nodes.get index = some node) (finished : ¬ cursor < node.children.size)
    (children : ∀ child ∈ node.children.toList, child ∈ processed)
    (budget : steps+1 ≤ tree.nodes.size*2+1) :
    ∃ after, outerScan seed root live () (none,tree,stack.push (index,cursor),steps) =
        .yield (none,after,stack,steps+1) ∧ Stage original (index::processed) after ∧
      Ranked rank after ∧ after.nodes.size = tree.nodes.size := by
  have currentPresent := (stage.outside index unprocessed).trans present
  obtain ⟨middle,kept,actual,middleRank,keptRank,capacity⟩ := GeneralBorrowGcRankedChildFold.complete
    rank node.children.toList seed tree root index live #[] ranked
    (ranked index node currentPresent) (by simp)
  have staged := GeneralBorrowGcDfsChildStage.fold original seed processed node.children.toList root index live children
    (none,tree,#[]) ⟨stage,by simp,by simp⟩
  rw [actual] at staged
  have afterPresent := (staged.1.outside index unprocessed).trans present
  have equation := GeneralBorrowGcDfsControl.finish_equation seed tree root index node live stack cursor steps
    currentPresent finished budget
  rw [←Array.forIn_toList,actual] at equation
  change middle.nodes.get index = some node at afterPresent
  simp only [afterPresent] at equation
  refine ⟨_,equation,GeneralBorrowGcDfsStage.finish original middle processed index node afterPresent kept staged.2.1 staged.1,
    GeneralBorrowGcStrictChildren.finish rank middle index node afterPresent kept keptRank middleRank,?_⟩
  exact (GeneralBorrowNodeUpdate.insert_existing_size middle.nodes index node _ afterPresent).trans capacity
end DuplicatePrefix.GeneralBorrowGcDfsRankedPostvisit
